use std::collections::HashSet;

use rustc_hash::FxHashMap;
use ttrpg_ast::Name;

use crate::ty::Ty;

/// What kind of block we're inside — determines permissions.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BlockKind {
    FunctionBody,
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
    /// `with_budget` body — provisions a scoped turn budget in a function.
    WithBudget,
    /// `on_apply` / `on_remove` lifecycle block inside a condition.
    /// Hook-like permissions minus `invocation()` and `turn`.
    LifecycleBlock,
    /// Inner blocks (if, match, etc.) inherit from enclosing real block.
    Inner,
}

impl BlockKind {
    pub fn allows_dice(&self) -> bool {
        matches!(
            self,
            BlockKind::FunctionBody
                | BlockKind::Mechanic
                | BlockKind::ActionResolve
                | BlockKind::ReactionResolve
                | BlockKind::HookResolve
                | BlockKind::WithBudget
                | BlockKind::LifecycleBlock
        )
    }

    pub fn allows_mutation(&self) -> bool {
        matches!(
            self,
            BlockKind::FunctionBody
                | BlockKind::ActionResolve
                | BlockKind::ReactionResolve
                | BlockKind::HookResolve
                | BlockKind::WithBudget
                | BlockKind::LifecycleBlock
        )
    }

    pub fn allows_invocation(&self) -> bool {
        matches!(
            self,
            BlockKind::ActionResolve | BlockKind::ReactionResolve | BlockKind::HookResolve
        )
    }

    pub fn allows_turn(&self) -> bool {
        matches!(
            self,
            BlockKind::ActionResolve
                | BlockKind::ReactionResolve
                | BlockKind::HookResolve
                | BlockKind::WithBudget
        )
    }

    /// Whether `return` statements are allowed. Permitted in imperative blocks
    /// (actions, reactions, hooks, functions, with_budget, lifecycle) but NOT
    /// in derives, mechanics, conditions, or prompts (expression-oriented).
    pub fn allows_return(&self) -> bool {
        matches!(
            self,
            BlockKind::FunctionBody
                | BlockKind::ActionResolve
                | BlockKind::ReactionResolve
                | BlockKind::HookResolve
                | BlockKind::WithBudget
                | BlockKind::LifecycleBlock
        )
    }

    /// Whether function calls (derives, mechanics, prompts, actions, reactions)
    /// are allowed. TriggerBinding only permits side-effect-free builtins.
    pub fn allows_calls(&self) -> bool {
        !matches!(self, BlockKind::TriggerBinding)
    }

    pub fn allows_emit(&self) -> bool {
        matches!(
            self,
            BlockKind::FunctionBody
                | BlockKind::ActionResolve
                | BlockKind::ReactionResolve
                | BlockKind::HookResolve
                | BlockKind::WithBudget
                | BlockKind::LifecycleBlock
        )
    }

    /// Whether `apply_condition`, `remove_condition`, and `revoke()` are allowed.
    /// Banned inside lifecycle blocks to prevent infinite recursion.
    pub fn allows_condition_manipulation(&self) -> bool {
        !matches!(self, BlockKind::LifecycleBlock)
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
    bindings: FxHashMap<Name, VarBinding>,
    /// Optional groups proven active for a given variable in this scope.
    /// Maps variable name → set of group names that are narrowed as active.
    narrowed_groups: FxHashMap<Name, HashSet<Name>>,
    /// Group aliases: (variable_name, alias_name) → real_group_name.
    group_aliases: FxHashMap<(Name, Name), Name>,
    /// Expected return type for this block (set on function/action/etc. scopes).
    return_type: Option<Ty>,
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
            bindings: FxHashMap::default(),
            narrowed_groups: FxHashMap::default(),
            group_aliases: FxHashMap::default(),
            return_type: None,
        });
    }

    pub fn push_with_return_type(&mut self, block_kind: BlockKind, return_type: Ty) {
        self.scopes.push(Scope {
            block_kind,
            bindings: FxHashMap::default(),
            narrowed_groups: FxHashMap::default(),
            group_aliases: FxHashMap::default(),
            return_type: Some(return_type),
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

    pub fn allows_invocation(&self) -> bool {
        self.current_block_kind()
            .is_some_and(|k| k.allows_invocation())
    }

    pub fn allows_emit(&self) -> bool {
        self.current_block_kind().is_some_and(|k| k.allows_emit())
    }

    pub fn allows_condition_manipulation(&self) -> bool {
        self.current_block_kind()
            .is_none_or(|k| k.allows_condition_manipulation())
    }

    pub fn allows_return(&self) -> bool {
        self.current_block_kind().is_some_and(|k| k.allows_return())
    }

    /// Find the return type of the enclosing block that set one (skipping Inner scopes).
    pub fn enclosing_return_type(&self) -> Option<&Ty> {
        for scope in self.scopes.iter().rev() {
            if let Some(ref ty) = scope.return_type {
                return Some(ty);
            }
            if scope.block_kind != BlockKind::Inner {
                return None;
            }
        }
        None
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
        let root = var.split('.').next().unwrap_or(var);
        for scope in self.scopes.iter().rev() {
            if let Some(groups) = scope.narrowed_groups.get(var) {
                if groups.contains(group) {
                    return true;
                }
            }
            // Stop at the scope that binds this variable — narrowing from
            // outer scopes applies to the outer binding, not a shadowed one.
            if scope.bindings.contains_key(root) {
                return false;
            }
        }
        false
    }

    /// Register a group alias: `var.alias` resolves to `var.real_group`.
    pub fn add_group_alias(&mut self, var: Name, alias: Name, real_group: Name) {
        debug_assert!(
            !self.scopes.is_empty(),
            "ScopeStack::add_group_alias called on empty stack"
        );
        if let Some(scope) = self.scopes.last_mut() {
            scope.group_aliases.insert((var, alias), real_group);
        }
    }

    /// Resolve a group alias for a variable, walking scopes innermost to outermost.
    /// Returns the real group name if `field` is an alias for a group on `var`.
    pub fn resolve_group_alias(&self, var: &str, field: &str) -> Option<Name> {
        let root = var.split('.').next().unwrap_or(var);
        let key = (Name::from(var), Name::from(field));
        for scope in self.scopes.iter().rev() {
            if let Some(real_group) = scope.group_aliases.get(&key) {
                return Some(real_group.clone());
            }
            // Stop at the scope that binds this variable
            if scope.bindings.contains_key(root) {
                return None;
            }
        }
        None
    }
}
