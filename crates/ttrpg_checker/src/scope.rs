use std::collections::{HashMap, HashSet};

use ttrpg_ast::Name;

use crate::ty::Ty;

/// What kind of block we're inside — determines permissions.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BlockKind {
    Derive,
    Mechanic,
    ActionResolve,
    ReactionResolve,
    HookResolve,
    Condition,
    Prompt,
    ModifyClause,
    /// Trigger/suppress binding expressions — disallows dice, mutations, turn
    /// access, action/reaction calls, prompts, and mechanic calls. Only
    /// side-effect-free builtins (floor, ceil, min, max, distance) are permitted.
    TriggerBinding,
    /// Inner blocks (if, match, etc.) inherit from enclosing real block.
    Inner,
}

impl BlockKind {
    pub fn allows_dice(&self) -> bool {
        matches!(
            self,
            BlockKind::Mechanic
                | BlockKind::ActionResolve
                | BlockKind::ReactionResolve
                | BlockKind::HookResolve
        )
    }

    pub fn allows_mutation(&self) -> bool {
        matches!(
            self,
            BlockKind::ActionResolve | BlockKind::ReactionResolve | BlockKind::HookResolve
        )
    }

    pub fn allows_turn(&self) -> bool {
        matches!(
            self,
            BlockKind::ActionResolve | BlockKind::ReactionResolve | BlockKind::HookResolve
        )
    }

    /// Whether function calls (derives, mechanics, prompts, actions, reactions)
    /// are allowed. TriggerBinding only permits side-effect-free builtins.
    pub fn allows_calls(&self) -> bool {
        !matches!(self, BlockKind::TriggerBinding)
    }
}

#[derive(Debug, Clone)]
pub struct VarBinding {
    pub ty: Ty,
    pub mutable: bool,
    /// True for `let`/`let mut` bindings; false for parameters and receivers.
    pub is_local: bool,
}

#[derive(Debug)]
struct Scope {
    block_kind: BlockKind,
    bindings: HashMap<Name, VarBinding>,
    /// Optional groups proven active for a given variable in this scope.
    /// Maps variable name → set of group names that are narrowed as active.
    narrowed_groups: HashMap<Name, HashSet<Name>>,
}

#[derive(Debug)]
pub struct ScopeStack {
    scopes: Vec<Scope>,
}

impl Default for ScopeStack {
    fn default() -> Self {
        Self::new()
    }
}

impl ScopeStack {
    pub fn new() -> Self {
        Self { scopes: Vec::new() }
    }

    pub fn push(&mut self, block_kind: BlockKind) {
        self.scopes.push(Scope {
            block_kind,
            bindings: HashMap::new(),
            narrowed_groups: HashMap::new(),
        });
    }

    pub fn pop(&mut self) {
        debug_assert!(
            !self.scopes.is_empty(),
            "ScopeStack::pop called on empty stack"
        );
        self.scopes.pop();
    }

    pub fn bind(&mut self, name: Name, binding: VarBinding) {
        debug_assert!(
            !self.scopes.is_empty(),
            "ScopeStack::bind called on empty stack"
        );
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
        self.current_block_kind().is_some_and(|k| k.allows_dice())
    }

    pub fn allows_mutation(&self) -> bool {
        self.current_block_kind()
            .is_some_and(|k| k.allows_mutation())
    }

    pub fn allows_turn(&self) -> bool {
        self.current_block_kind().is_some_and(|k| k.allows_turn())
    }

    pub fn allows_calls(&self) -> bool {
        self.current_block_kind().is_none_or(|k| k.allows_calls())
    }

    /// Check if a name is already bound in the innermost scope.
    pub fn has_in_current_scope(&self, name: &str) -> bool {
        self.scopes
            .last()
            .is_some_and(|s| s.bindings.contains_key(name))
    }

    /// Mark entity-typed bindings in the current scope as non-local.
    ///
    /// Used for for-loop pattern bindings so that entity field mutation
    /// works through them (e.g. `for target in targets { target.HP -= 5 }`),
    /// matching the behavior of function parameters. Only entity-typed
    /// bindings are promoted — non-entity bindings (structs, lists, etc.)
    /// remain local so the immutable-local guard still applies.
    pub fn mark_current_scope_entities_non_local(&mut self) {
        debug_assert!(
            !self.scopes.is_empty(),
            "ScopeStack::mark_current_scope_entities_non_local called on empty stack"
        );
        if let Some(scope) = self.scopes.last_mut() {
            for binding in scope.bindings.values_mut() {
                if binding.ty.is_entity() {
                    binding.is_local = false;
                }
            }
        }
    }

    /// Record that a variable's optional group is proven active in the current scope.
    pub fn narrow_group(&mut self, var: Name, group: Name) {
        debug_assert!(
            !self.scopes.is_empty(),
            "ScopeStack::narrow_group called on empty stack"
        );
        if let Some(scope) = self.scopes.last_mut() {
            scope.narrowed_groups.entry(var).or_default().insert(group);
        }
    }

    /// Check whether an optional group is narrowed as active for a variable,
    /// walking scopes innermost to outermost.
    pub fn is_group_narrowed(&self, var: &str, group: &str) -> bool {
        for scope in self.scopes.iter().rev() {
            if let Some(groups) = scope.narrowed_groups.get(var) {
                if groups.contains(group) {
                    return true;
                }
            }
            // Stop at the scope that binds this variable — narrowing from
            // outer scopes applies to the outer binding, not a shadowed one.
            if scope.bindings.contains_key(var) {
                return false;
            }
        }
        false
    }
}
