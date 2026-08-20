/-!
# Rls Off Implies No Row Protection
Category: Proof-Carrying Apps
Target: PCA.Invariant.rls_off_implies_no_row_protection
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false

universe u v

namespace PCA

/-- A row-level-security policy, in the style of a PostgreSQL `CREATE POLICY`
statement: it names the roles it applies to (`appliesTo`) and carries a `USING`
predicate that a row must satisfy for the policy to grant visibility. -/
structure Policy (Role : Type u) (Row : Type v) where
  /-- Roles this policy is declared `TO`. -/
  appliesTo : Role → Bool
  /-- The `USING` clause: which rows the policy exposes. -/
  usingCheck : Row → Bool

/-- A table together with its isolation configuration: whether row-level
security is enabled, whether it is *forced* (so that the table owner is not
exempt), who owns the table, and the list of permissive policies attached. -/
structure Table (Role : Type u) (Row : Type v) where
  /-- `ALTER TABLE ... ENABLE ROW LEVEL SECURITY`. -/
  rlsEnabled : Bool
  /-- `ALTER TABLE ... FORCE ROW LEVEL SECURITY`. -/
  forceRls : Bool
  /-- The owner of the table. -/
  owner : Role
  /-- The permissive policies attached to the table. -/
  policies : List (Policy Role Row)

variable {Role : Type u} {Row : Type v} [DecidableEq Role]

/-- The visibility semantics of the isolation engine: a row is visible to a
role when row-level security is off, or the role is an exempt owner, or some
permissive policy applicable to the role admits the row. -/
def Table.visible (t : Table Role Row) (role : Role) (r : Row) : Bool :=
  !t.rlsEnabled ||
    (decide (role = t.owner) && !t.forceRls) ||
    t.policies.any (fun p => p.appliesTo role && p.usingCheck r)

/-- A row is *protected* when the engine hides it from at least one role. -/
def Table.RowProtected (t : Table Role Row) (r : Row) : Prop :=
  ∃ role : Role, t.visible role r = false

/-- The rows of a table that a given role may observe. -/
def Table.query (t : Table Role Row) (role : Role) (rows : List Row) : List Row :=
  rows.filter (fun r => t.visible role r)

namespace Invariant

/-- **Main invariant.** If row-level security is disabled on a table, then no
row of that table is protected: every role sees every row.

No Mathlib lemma states this; it is a fact about the isolation model defined
above, and unfolds to a boolean tautology once `rlsEnabled = false`. -/
theorem rls_off_implies_no_row_protection
    (t : Table Role Row) (h : t.rlsEnabled = false) (r : Row) :
    ¬ t.RowProtected r := by
  simp [Table.RowProtected, Table.visible, h]

/-- Equivalent phrasing: with row-level security off, every role sees every
row. -/
theorem rls_off_all_visible
    (t : Table Role Row) (h : t.rlsEnabled = false) (role : Role) (r : Row) :
    t.visible role r = true := by
  simp [Table.visible, h]

/-- Consequence for queries: with row-level security off, a query filters
nothing away. -/
theorem rls_off_query_eq_all
    (t : Table Role Row) (h : t.rlsEnabled = false) (role : Role) (rows : List Row) :
    t.query role rows = rows :=
  List.filter_eq_self.2 (fun r _ => rls_off_all_visible t h role r)

/-- Contrapositive: if any row is protected, row-level security must be on. -/
theorem row_protected_implies_rls_on
    (t : Table Role Row) (r : Row) (hp : t.RowProtected r) :
    t.rlsEnabled = true := by
  rcases Bool.eq_false_or_eq_true t.rlsEnabled with h | h
  · exact h
  · exact absurd hp (rls_off_implies_no_row_protection t h r)

/-- The invariant is not vacuous: with row-level security forced on and no
policies, every row is protected. -/
theorem exists_row_protected_of_rls_on
    (t : Table Role Row) (r : Row) (role : Role)
    (h : t.rlsEnabled = true) (hf : t.forceRls = true) (hp : t.policies = []) :
    t.RowProtected r :=
  ⟨role, by simp [Table.visible, h, hf, hp]⟩

end Invariant

end PCA

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

