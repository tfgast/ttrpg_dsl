use std::collections::HashMap;

use crate::ty::Ty;

/// What kind of block we're inside — determines permissions.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BlockKind {
    Derive,
    Mechanic,
    ActionResolve,
    ReactionResolve,
    Condition,
    Prompt,
    ModifyClause,
    /// Inner blocks (if, match, etc.) inherit from enclosing real block.
    Inner,
}

impl BlockKind {
    pub fn allows_dice(&self) -> bool {
        matches!(
            self,
            BlockKind::Mechanic | BlockKind::ActionResolve | BlockKind::ReactionResolve
        )
    }

    pub fn allows_mutation(&self) -> bool {
        matches!(
            self,
            BlockKind::ActionResolve | BlockKind::ReactionResolve
        )
    }

    pub fn allows_turn(&self) -> bool {
        matches!(
            self,
            BlockKind::ActionResolve | BlockKind::ReactionResolve
        )
    }
}

#[derive(Debug, Clone)]
pub struct VarBinding {
    pub ty: Ty,
    pub mutable: bool,
}

#[derive(Debug)]
struct Scope {
    block_kind: BlockKind,
    bindings: HashMap<String, VarBinding>,
}

#[derive(Debug)]
pub struct ScopeStack {
    scopes: Vec<Scope>,
}

impl ScopeStack {
    pub fn new() -> Self {
        Self { scopes: Vec::new() }
    }

    pub fn push(&mut self, block_kind: BlockKind) {
        self.scopes.push(Scope {
            block_kind,
            bindings: HashMap::new(),
        });
    }

    pub fn pop(&mut self) {
        self.scopes.pop();
    }

    pub fn bind(&mut self, name: String, binding: VarBinding) {
        if let Some(scope) = self.scopes.last_mut() {
            scope.bindings.insert(name, binding);
        }
    }

    /// Look up a variable, walking scopes innermost to outermost.
    pub fn lookup(&self, name: &str) -> Option<&VarBinding> {
        for scope in self.scopes.iter().rev() {
            if let Some(binding) = scope.bindings.get(name) {
                return Some(binding);
            }
        }
        None
    }

    /// Find the enclosing real block kind (skipping Inner scopes).
    pub fn current_block_kind(&self) -> Option<BlockKind> {
        for scope in self.scopes.iter().rev() {
            if scope.block_kind != BlockKind::Inner {
                return Some(scope.block_kind);
            }
        }
        None
    }

    pub fn allows_dice(&self) -> bool {
        self.current_block_kind()
            .map_or(false, |k| k.allows_dice())
    }

    pub fn allows_mutation(&self) -> bool {
        self.current_block_kind()
            .map_or(false, |k| k.allows_mutation())
    }

    pub fn allows_turn(&self) -> bool {
        self.current_block_kind()
            .map_or(false, |k| k.allows_turn())
    }
}
