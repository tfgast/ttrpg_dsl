use std::any::Any;
use std::collections::{BTreeMap, BTreeSet};
use std::fmt;
use std::sync::Arc;

use ttrpg_ast::DiceFilter;

use crate::state::EntityRef;

// ── Dice pipeline types ─────────────────────────────────────────

/// A dice expression that has not yet been rolled.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DiceExpr {
    pub count: u32,
    pub sides: u32,
    pub filter: Option<DiceFilter>,
    pub modifier: i64,
}

/// The result of rolling a dice expression.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RollResult {
    pub expr: DiceExpr,
    pub dice: Vec<i64>,
    pub kept: Vec<i64>,
    pub modifier: i64,
    pub total: i64,
    pub unmodified: i64,
}

// ── Turn economy ────────────────────────────────────────────────

/// The action economy budget for a single turn.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TurnBudget {
    pub actions: i64,
    pub bonus_actions: i64,
    pub reactions: i64,
    pub movement: i64,
    pub free_interactions: i64,
}

impl Default for TurnBudget {
    fn default() -> Self {
        TurnBudget {
            actions: 1,
            bonus_actions: 1,
            reactions: 1,
            movement: 0,
            free_interactions: 1,
        }
    }
}

// ── Duration ────────────────────────────────────────────────────

/// Duration values for conditions and effects.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum DurationValue {
    EndOfTurn,
    StartOfNextTurn,
    Rounds(i64),
    Minutes(i64),
    Indefinite,
}

// ── Position ────────────────────────────────────────────────────

/// An opaque position value owned by the host.
///
/// Uses `Arc` so `Value` can derive `Clone`. `Send + Sync` bounds
/// future-proof for potential multi-threaded host integrations.
///
/// `Ord` orders by `Arc` pointer (deterministic but arbitrary) — the
/// checker prevents `Position` in sets/maps, so this is a safety net.
/// `PartialEq` uses `Arc::ptr_eq` — same allocation means same position.
/// For cross-object comparison, the evaluator routes through `value_eq()`
/// which delegates to `StateProvider::position_eq`.
pub struct PositionValue(pub Arc<dyn Any + Send + Sync>);

impl Clone for PositionValue {
    fn clone(&self) -> Self {
        PositionValue(Arc::clone(&self.0))
    }
}

impl fmt::Debug for PositionValue {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Position({:p})", Arc::as_ptr(&self.0))
    }
}

impl PartialEq for PositionValue {
    fn eq(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.0, &other.0)
    }
}

impl Eq for PositionValue {}

impl PartialOrd for PositionValue {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for PositionValue {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        let a = Arc::as_ptr(&self.0) as *const () as usize;
        let b = Arc::as_ptr(&other.0) as *const () as usize;
        a.cmp(&b)
    }
}

// ── Value enum ──────────────────────────────────────────────────

/// The unified runtime value type for the interpreter.
///
/// All expressions evaluate to a `Value`. Effects carry `Value`s.
/// The host sends `Value`s back via responses.
#[derive(Debug, Clone)]
pub enum Value {
    // Primitives
    Int(i64),
    Float(f64),
    Bool(bool),
    Str(String),
    None,

    // Dice pipeline
    DiceExpr(DiceExpr),
    RollResult(RollResult),

    // Composites
    List(Vec<Value>),
    Set(BTreeSet<Value>),
    Map(BTreeMap<Value, Value>),
    Option(Option<Box<Value>>),

    // Structured
    Struct {
        name: String,
        fields: BTreeMap<String, Value>,
    },
    Entity(EntityRef),
    EnumVariant {
        enum_name: String,
        variant: String,
        fields: BTreeMap<String, Value>,
    },

    // Opaque
    Position(PositionValue),

    // Special
    TurnBudget(TurnBudget),
    Duration(DurationValue),
    Condition(String),

    /// Internal: an enum type name used as a namespace for qualified variant
    /// access (e.g., `Duration.rounds`). Not a user-facing value — only
    /// produced by `eval_ident` when an identifier resolves to an enum type.
    EnumNamespace(String),
}

// ── Discriminant ordering ───────────────────────────────────────

/// Returns a numeric discriminant for cross-variant ordering.
fn discriminant(v: &Value) -> u8 {
    match v {
        Value::None => 0,
        Value::Bool(_) => 1,
        Value::Int(_) => 2,
        Value::Float(_) => 3,
        Value::Str(_) => 4,
        Value::DiceExpr(_) => 5,
        Value::RollResult(_) => 6,
        Value::List(_) => 7,
        Value::Set(_) => 8,
        Value::Map(_) => 9,
        Value::Option(_) => 10,
        Value::Struct { .. } => 11,
        Value::Entity(_) => 12,
        Value::EnumVariant { .. } => 13,
        Value::Position(_) => 14,
        Value::TurnBudget(_) => 15,
        Value::Duration(_) => 16,
        Value::Condition(_) => 17,
        Value::EnumNamespace(_) => 18,
    }
}

// ── PartialEq / Eq ─────────────────────────────────────────────
//
// Structural equality for BTreeSet/BTreeMap invariants.
// Float uses `to_bits()` (NaN == NaN, +0 != -0).
// Position uses `Arc::ptr_eq`.
//
// Runtime equality checks use `value_eq()` in eval.rs instead,
// which gives user-expected semantics (Float: -0.0 == +0.0,
// Position: delegated to StateProvider::position_eq).

impl PartialEq for Value {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Value::None, Value::None) => true,
            (Value::Bool(a), Value::Bool(b)) => a == b,
            (Value::Int(a), Value::Int(b)) => a == b,
            (Value::Float(a), Value::Float(b)) => a.to_bits() == b.to_bits(),
            (Value::Str(a), Value::Str(b)) => a == b,
            (Value::DiceExpr(a), Value::DiceExpr(b)) => a == b,
            (Value::RollResult(a), Value::RollResult(b)) => a == b,
            (Value::List(a), Value::List(b)) => a == b,
            (Value::Set(a), Value::Set(b)) => a == b,
            (Value::Map(a), Value::Map(b)) => a == b,
            (Value::Option(a), Value::Option(b)) => a == b,
            (
                Value::Struct {
                    name: n1,
                    fields: f1,
                },
                Value::Struct {
                    name: n2,
                    fields: f2,
                },
            ) => n1 == n2 && f1 == f2,
            (Value::Entity(a), Value::Entity(b)) => a == b,
            (
                Value::EnumVariant {
                    enum_name: e1,
                    variant: v1,
                    fields: f1,
                },
                Value::EnumVariant {
                    enum_name: e2,
                    variant: v2,
                    fields: f2,
                },
            ) => e1 == e2 && v1 == v2 && f1 == f2,
            (Value::Position(a), Value::Position(b)) => a == b,
            (Value::TurnBudget(a), Value::TurnBudget(b)) => a == b,
            (Value::Duration(a), Value::Duration(b)) => a == b,
            (Value::Condition(a), Value::Condition(b)) => a == b,
            (Value::EnumNamespace(a), Value::EnumNamespace(b)) => a == b,
            _ => false,
        }
    }
}

impl Eq for Value {}

// ── PartialOrd / Ord ────────────────────────────────────────────
//
// Cross-variant: discriminant ordering.
// Within variant: natural ordering. Float uses `total_cmp`.

impl PartialOrd for Value {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Value {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        use std::cmp::Ordering;

        let da = discriminant(self);
        let db = discriminant(other);
        if da != db {
            return da.cmp(&db);
        }

        match (self, other) {
            (Value::None, Value::None) => Ordering::Equal,
            (Value::Bool(a), Value::Bool(b)) => a.cmp(b),
            (Value::Int(a), Value::Int(b)) => a.cmp(b),
            (Value::Float(a), Value::Float(b)) => a.total_cmp(b),
            (Value::Str(a), Value::Str(b)) => a.cmp(b),
            (Value::DiceExpr(a), Value::DiceExpr(b)) => dice_expr_cmp(a, b),
            (Value::RollResult(a), Value::RollResult(b)) => roll_result_cmp(a, b),
            (Value::List(a), Value::List(b)) => a.cmp(b),
            (Value::Set(a), Value::Set(b)) => a.cmp(b),
            (Value::Map(a), Value::Map(b)) => map_cmp(a, b),
            (Value::Option(a), Value::Option(b)) => a.cmp(b),
            (
                Value::Struct {
                    name: n1,
                    fields: f1,
                },
                Value::Struct {
                    name: n2,
                    fields: f2,
                },
            ) => n1.cmp(n2).then_with(|| btree_map_cmp(f1, f2)),
            (Value::Entity(a), Value::Entity(b)) => a.0.cmp(&b.0),
            (
                Value::EnumVariant {
                    enum_name: e1,
                    variant: v1,
                    fields: f1,
                },
                Value::EnumVariant {
                    enum_name: e2,
                    variant: v2,
                    fields: f2,
                },
            ) => e1
                .cmp(e2)
                .then_with(|| v1.cmp(v2))
                .then_with(|| btree_map_cmp(f1, f2)),
            (Value::Position(a), Value::Position(b)) => a.cmp(b),
            (Value::TurnBudget(a), Value::TurnBudget(b)) => turn_budget_cmp(a, b),
            (Value::Duration(a), Value::Duration(b)) => a.cmp(b),
            (Value::Condition(a), Value::Condition(b)) => a.cmp(b),
            (Value::EnumNamespace(a), Value::EnumNamespace(b)) => a.cmp(b),
            // Same discriminant guarantees same variant.
            _ => unreachable!(),
        }
    }
}

fn dice_expr_cmp(a: &DiceExpr, b: &DiceExpr) -> std::cmp::Ordering {
    a.count
        .cmp(&b.count)
        .then_with(|| a.sides.cmp(&b.sides))
        .then_with(|| a.modifier.cmp(&b.modifier))
        .then_with(|| a.filter.cmp(&b.filter))
}

fn roll_result_cmp(a: &RollResult, b: &RollResult) -> std::cmp::Ordering {
    dice_expr_cmp(&a.expr, &b.expr)
        .then_with(|| a.dice.cmp(&b.dice))
        .then_with(|| a.kept.cmp(&b.kept))
        .then_with(|| a.modifier.cmp(&b.modifier))
        .then_with(|| a.total.cmp(&b.total))
        .then_with(|| a.unmodified.cmp(&b.unmodified))
}

fn turn_budget_cmp(a: &TurnBudget, b: &TurnBudget) -> std::cmp::Ordering {
    a.actions
        .cmp(&b.actions)
        .then_with(|| a.bonus_actions.cmp(&b.bonus_actions))
        .then_with(|| a.reactions.cmp(&b.reactions))
        .then_with(|| a.movement.cmp(&b.movement))
        .then_with(|| a.free_interactions.cmp(&b.free_interactions))
}

fn btree_map_cmp(a: &BTreeMap<String, Value>, b: &BTreeMap<String, Value>) -> std::cmp::Ordering {
    let mut ai = a.iter();
    let mut bi = b.iter();
    loop {
        match (ai.next(), bi.next()) {
            (None, None) => return std::cmp::Ordering::Equal,
            (None, Some(_)) => return std::cmp::Ordering::Less,
            (Some(_), None) => return std::cmp::Ordering::Greater,
            (Some((ak, av)), Some((bk, bv))) => {
                let c = ak.cmp(bk).then_with(|| av.cmp(bv));
                if c != std::cmp::Ordering::Equal {
                    return c;
                }
            }
        }
    }
}

fn map_cmp(a: &BTreeMap<Value, Value>, b: &BTreeMap<Value, Value>) -> std::cmp::Ordering {
    let mut ai = a.iter();
    let mut bi = b.iter();
    loop {
        match (ai.next(), bi.next()) {
            (None, None) => return std::cmp::Ordering::Equal,
            (None, Some(_)) => return std::cmp::Ordering::Less,
            (Some(_), None) => return std::cmp::Ordering::Greater,
            (Some((ak, av)), Some((bk, bv))) => {
                let c = ak.cmp(bk).then_with(|| av.cmp(bv));
                if c != std::cmp::Ordering::Equal {
                    return c;
                }
            }
        }
    }
}

// ── Hash ────────────────────────────────────────────────────────
//
// Required for BTreeSet/BTreeMap usage in some contexts.
// Consistent with Eq: Float uses to_bits().

impl std::hash::Hash for Value {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        discriminant(self).hash(state);
        match self {
            Value::None => {}
            Value::Bool(v) => v.hash(state),
            Value::Int(v) => v.hash(state),
            Value::Float(v) => v.to_bits().hash(state),
            Value::Str(v) => v.hash(state),
            Value::DiceExpr(v) => {
                v.count.hash(state);
                v.sides.hash(state);
                v.filter.hash(state);
                v.modifier.hash(state);
            }
            Value::RollResult(v) => {
                v.expr.count.hash(state);
                v.expr.sides.hash(state);
                v.expr.filter.hash(state);
                v.expr.modifier.hash(state);
                v.dice.hash(state);
                v.kept.hash(state);
                v.modifier.hash(state);
                v.total.hash(state);
                v.unmodified.hash(state);
            }
            Value::List(v) => v.hash(state),
            Value::Set(v) => {
                for item in v {
                    item.hash(state);
                }
            }
            Value::Map(v) => {
                for (k, val) in v {
                    k.hash(state);
                    val.hash(state);
                }
            }
            Value::Option(v) => v.hash(state),
            Value::Struct { name, fields } => {
                name.hash(state);
                for (k, v) in fields {
                    k.hash(state);
                    v.hash(state);
                }
            }
            Value::Entity(v) => v.0.hash(state),
            Value::EnumVariant {
                enum_name,
                variant,
                fields,
            } => {
                enum_name.hash(state);
                variant.hash(state);
                for (k, v) in fields {
                    k.hash(state);
                    v.hash(state);
                }
            }
            Value::Position(v) => {
                (Arc::as_ptr(&v.0) as *const () as usize).hash(state);
            }
            Value::TurnBudget(v) => {
                v.actions.hash(state);
                v.bonus_actions.hash(state);
                v.reactions.hash(state);
                v.movement.hash(state);
                v.free_interactions.hash(state);
            }
            Value::Duration(v) => v.hash(state),
            Value::Condition(v) => v.hash(state),
            Value::EnumNamespace(v) => v.hash(state),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // ── Primitive equality ──────────────────────────────────────

    #[test]
    fn int_equality() {
        assert_eq!(Value::Int(42), Value::Int(42));
        assert_ne!(Value::Int(42), Value::Int(43));
    }

    #[test]
    fn float_structural_equality_to_bits() {
        // NaN == NaN for structural (BTreeSet) purposes
        assert_eq!(Value::Float(f64::NAN), Value::Float(f64::NAN));
        // +0 != -0 for structural purposes
        assert_ne!(Value::Float(0.0), Value::Float(-0.0));
        // Normal equality
        assert_eq!(Value::Float(3.14), Value::Float(3.14));
    }

    #[test]
    fn bool_equality() {
        assert_eq!(Value::Bool(true), Value::Bool(true));
        assert_ne!(Value::Bool(true), Value::Bool(false));
    }

    #[test]
    fn str_equality() {
        assert_eq!(
            Value::Str("hello".to_string()),
            Value::Str("hello".to_string())
        );
        assert_ne!(
            Value::Str("hello".to_string()),
            Value::Str("world".to_string())
        );
    }

    #[test]
    fn none_equality() {
        assert_eq!(Value::None, Value::None);
    }

    // ── Cross-variant inequality ────────────────────────────────

    #[test]
    fn different_variants_not_equal() {
        assert_ne!(Value::Int(0), Value::Float(0.0));
        assert_ne!(Value::Int(1), Value::Bool(true));
        assert_ne!(Value::None, Value::Int(0));
    }

    // ── Composite equality ──────────────────────────────────────

    #[test]
    fn list_equality() {
        let a = Value::List(vec![Value::Int(1), Value::Int(2)]);
        let b = Value::List(vec![Value::Int(1), Value::Int(2)]);
        let c = Value::List(vec![Value::Int(1), Value::Int(3)]);
        assert_eq!(a, b);
        assert_ne!(a, c);
    }

    #[test]
    fn set_equality() {
        let mut s1 = BTreeSet::new();
        s1.insert(Value::Int(1));
        s1.insert(Value::Int(2));
        let mut s2 = BTreeSet::new();
        s2.insert(Value::Int(2));
        s2.insert(Value::Int(1));
        assert_eq!(Value::Set(s1), Value::Set(s2));
    }

    #[test]
    fn map_equality() {
        let mut m1 = BTreeMap::new();
        m1.insert(Value::Str("a".into()), Value::Int(1));
        let mut m2 = BTreeMap::new();
        m2.insert(Value::Str("a".into()), Value::Int(1));
        assert_eq!(Value::Map(m1), Value::Map(m2));
    }

    #[test]
    fn struct_equality() {
        let mut f1 = BTreeMap::new();
        f1.insert("x".into(), Value::Int(10));
        let mut f2 = BTreeMap::new();
        f2.insert("x".into(), Value::Int(10));
        assert_eq!(
            Value::Struct {
                name: "Point".into(),
                fields: f1
            },
            Value::Struct {
                name: "Point".into(),
                fields: f2
            }
        );
    }

    #[test]
    fn enum_variant_equality() {
        let mut f1 = BTreeMap::new();
        f1.insert("value".into(), Value::Int(3));
        let mut f2 = BTreeMap::new();
        f2.insert("value".into(), Value::Int(3));
        assert_eq!(
            Value::EnumVariant {
                enum_name: "Duration".into(),
                variant: "rounds".into(),
                fields: f1
            },
            Value::EnumVariant {
                enum_name: "Duration".into(),
                variant: "rounds".into(),
                fields: f2
            }
        );
    }

    // ── Ordering ────────────────────────────────────────────────

    #[test]
    fn cross_variant_ordering() {
        // None < Bool < Int < Float < Str
        assert!(Value::None < Value::Bool(false));
        assert!(Value::Bool(true) < Value::Int(0));
        assert!(Value::Int(0) < Value::Float(0.0));
        assert!(Value::Float(0.0) < Value::Str("".into()));
    }

    #[test]
    fn int_ordering() {
        assert!(Value::Int(1) < Value::Int(2));
        assert!(Value::Int(-1) < Value::Int(0));
    }

    #[test]
    fn float_ordering_total_cmp() {
        // total_cmp: -0.0 < +0.0
        assert!(Value::Float(-0.0) < Value::Float(0.0));
        assert!(Value::Float(1.0) < Value::Float(2.0));
    }

    #[test]
    fn str_ordering() {
        assert!(Value::Str("abc".into()) < Value::Str("abd".into()));
    }

    #[test]
    fn list_ordering() {
        let a = Value::List(vec![Value::Int(1), Value::Int(2)]);
        let b = Value::List(vec![Value::Int(1), Value::Int(3)]);
        assert!(a < b);
    }

    // ── Position ────────────────────────────────────────────────

    #[test]
    fn position_ptr_eq() {
        let pos: Arc<dyn Any + Send + Sync> = Arc::new((1i64, 2i64));
        let v1 = Value::Position(PositionValue(Arc::clone(&pos)));
        let v2 = Value::Position(PositionValue(Arc::clone(&pos)));
        assert_eq!(v1, v2);

        let other: Arc<dyn Any + Send + Sync> = Arc::new((1i64, 2i64));
        let v3 = Value::Position(PositionValue(other));
        assert_ne!(v1, v3); // different Arc, even if same data
    }

    // ── Value in BTreeSet ───────────────────────────────────────

    #[test]
    fn value_in_btreeset() {
        let mut set = BTreeSet::new();
        set.insert(Value::Int(1));
        set.insert(Value::Int(2));
        set.insert(Value::Int(1)); // duplicate
        assert_eq!(set.len(), 2);
    }

    #[test]
    fn value_in_btreemap() {
        let mut map = BTreeMap::new();
        map.insert(Value::Str("key".into()), Value::Int(42));
        assert_eq!(map.get(&Value::Str("key".into())), Some(&Value::Int(42)));
    }

    // ── DiceExpr / RollResult construction ──────────────────────

    #[test]
    fn dice_expr_construction() {
        let expr = DiceExpr {
            count: 2,
            sides: 6,
            filter: None,
            modifier: 3,
        };
        assert_eq!(expr.count, 2);
        assert_eq!(expr.sides, 6);
        assert_eq!(expr.modifier, 3);
    }

    #[test]
    fn roll_result_construction() {
        let expr = DiceExpr {
            count: 2,
            sides: 6,
            filter: None,
            modifier: 3,
        };
        let result = RollResult {
            expr: expr.clone(),
            dice: vec![4, 5],
            kept: vec![4, 5],
            modifier: 3,
            total: 12,
            unmodified: 9,
        };
        assert_eq!(result.total, 12);
        assert_eq!(result.unmodified, 9);
    }

    // ── TurnBudget ──────────────────────────────────────────────

    #[test]
    fn turn_budget_default() {
        let budget = TurnBudget::default();
        assert_eq!(budget.actions, 1);
        assert_eq!(budget.bonus_actions, 1);
        assert_eq!(budget.reactions, 1);
    }

    // ── DurationValue ───────────────────────────────────────────

    #[test]
    fn duration_equality() {
        assert_eq!(DurationValue::Rounds(3), DurationValue::Rounds(3));
        assert_ne!(DurationValue::Rounds(3), DurationValue::Minutes(3));
        assert_eq!(DurationValue::Indefinite, DurationValue::Indefinite);
    }

    // ── Option variant ──────────────────────────────────────────

    #[test]
    fn option_value() {
        let some = Value::Option(Some(Box::new(Value::Int(42))));
        let none = Value::Option(None);
        assert_ne!(some, none);
        assert_eq!(
            Value::Option(Some(Box::new(Value::Int(42)))),
            Value::Option(Some(Box::new(Value::Int(42))))
        );
    }

    // ── Ord/Eq contract ─────────────────────────────────────────
    //
    // Verify: cmp(a, b) == Equal iff a == b for all variant pairs.

    /// Helper: assert the Ord/Eq contract holds for a pair of values.
    fn assert_ord_eq_consistent(a: &Value, b: &Value) {
        let eq = a == b;
        let ord_eq = a.cmp(b) == std::cmp::Ordering::Equal;
        assert_eq!(
            eq, ord_eq,
            "Ord/Eq contract violation: ({:?}).eq({:?}) = {}, cmp = {:?}",
            a, b, eq, a.cmp(b)
        );
    }

    #[test]
    fn ord_eq_contract_roll_result_same_total_different_dice() {
        let expr = DiceExpr {
            count: 2,
            sides: 6,
            filter: None,
            modifier: 0,
        };
        let r1 = Value::RollResult(RollResult {
            expr: expr.clone(),
            dice: vec![3, 4],
            kept: vec![3, 4],
            modifier: 0,
            total: 7,
            unmodified: 7,
        });
        let r2 = Value::RollResult(RollResult {
            expr: expr.clone(),
            dice: vec![2, 5],
            kept: vec![2, 5],
            modifier: 0,
            total: 7,
            unmodified: 7,
        });
        // Same total but different dice — must be != and cmp != Equal
        assert_ne!(r1, r2);
        assert_ord_eq_consistent(&r1, &r2);
    }

    #[test]
    fn ord_eq_contract_all_variants() {
        let pos: Arc<dyn Any + Send + Sync> = Arc::new(42i64);
        let expr = DiceExpr {
            count: 1,
            sides: 20,
            filter: None,
            modifier: 5,
        };

        // Build pairs of (equal, different) for each variant
        let pairs: Vec<(Value, Value, Value)> = vec![
            (Value::None, Value::None, Value::Int(0)),
            (Value::Bool(true), Value::Bool(true), Value::Bool(false)),
            (Value::Int(42), Value::Int(42), Value::Int(43)),
            (Value::Float(3.14), Value::Float(3.14), Value::Float(2.71)),
            (
                Value::Str("a".into()),
                Value::Str("a".into()),
                Value::Str("b".into()),
            ),
            (
                Value::DiceExpr(expr.clone()),
                Value::DiceExpr(expr.clone()),
                Value::DiceExpr(DiceExpr {
                    count: 2,
                    sides: 20,
                    filter: None,
                    modifier: 5,
                }),
            ),
            (
                Value::RollResult(RollResult {
                    expr: expr.clone(),
                    dice: vec![10],
                    kept: vec![10],
                    modifier: 5,
                    total: 15,
                    unmodified: 10,
                }),
                Value::RollResult(RollResult {
                    expr: expr.clone(),
                    dice: vec![10],
                    kept: vec![10],
                    modifier: 5,
                    total: 15,
                    unmodified: 10,
                }),
                Value::RollResult(RollResult {
                    expr: expr.clone(),
                    dice: vec![11],
                    kept: vec![11],
                    modifier: 5,
                    total: 16,
                    unmodified: 11,
                }),
            ),
            (
                Value::List(vec![Value::Int(1)]),
                Value::List(vec![Value::Int(1)]),
                Value::List(vec![Value::Int(2)]),
            ),
            (Value::Entity(EntityRef(1)), Value::Entity(EntityRef(1)), Value::Entity(EntityRef(2))),
            (
                Value::Position(PositionValue(Arc::clone(&pos))),
                Value::Position(PositionValue(Arc::clone(&pos))),
                Value::Position(PositionValue(Arc::new(99i64))),
            ),
            (Value::Condition("Prone".into()), Value::Condition("Prone".into()), Value::Condition("Stunned".into())),
            (
                Value::Duration(DurationValue::Rounds(3)),
                Value::Duration(DurationValue::Rounds(3)),
                Value::Duration(DurationValue::Rounds(5)),
            ),
        ];

        for (a, b_eq, b_ne) in &pairs {
            assert_ord_eq_consistent(a, b_eq);
            assert_ord_eq_consistent(a, b_ne);
        }
    }
}
