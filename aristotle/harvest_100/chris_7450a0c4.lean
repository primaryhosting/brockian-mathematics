/-!
# Rls Off Implies No Row Protection
Category: Proof-Carrying Apps
Target: PCA.Invariant.rls_off_implies_no_row_protection
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false

namespace PCA

/-- A principal (role) issuing a query against the database. -/
abbrev Role := String

/-- A row-level-security policy: a boolean predicate saying, for a given role,
which rows that policy grants access to. -/
structure Policy (Row : Type) where
  /-- `applies r row` holds when the policy grants role `r` access to `row`. -/
  applies : Role → Row → Bool

/-- A table of the isolation engine's model: its rows, whether row-level security
(RLS) is switched on for it, and the list of RLS policies attached to it. -/
structure Table (Row : Type) where
  /-- The rows stored in the table. -/
  rows : List Row
  /-- Whether row-level security is enabled for this table. -/
  rlsEnabled : Bool
  /-- The RLS policies attached to the table. -/
  policies : List (Policy Row)

variable {Row : Type}

/-- The visibility semantics of the engine: when RLS is off every row is visible to
every role; when RLS is on a row is visible exactly when some attached policy grants
access to it. -/
def Table.visible (t : Table Row) (r : Role) (row : Row) : Bool :=
  !t.rlsEnabled || t.policies.any (fun p => p.applies r row)

/-- The result of a full-table scan performed by role `r`: the rows of `t` that are
visible to `r`. -/
def Table.select (t : Table Row) (r : Role) : List Row :=
  t.rows.filter (t.visible r)

/-- A row is *protected* when at least one role is denied access to it. -/
def Table.IsProtected (t : Table Row) (row : Row) : Prop :=
  ∃ r : Role, t.visible r row = false

namespace Invariant

/-- **Soundness of the isolation model with RLS switched off.**

If row-level security is disabled on a table, then the table offers no row protection
whatsoever: no row (whether stored in the table or not) is protected, and every role's
scan of the table returns *all* of its rows.

The proof goes through the equivalent positive statement: `visible` is the disjunction
`!rlsEnabled || …`, whose left disjunct is `true` when `rlsEnabled = false`, so
`visible` can never evaluate to `false`. -/
theorem rls_off_implies_no_row_protection (t : Table Row) (h : t.rlsEnabled = false) :
    (∀ row : Row, ¬ t.IsProtected row) ∧ (∀ r : Role, t.select r = t.rows) := by
  have hvis : ∀ (r : Role) (row : Row), t.visible r row = true := by
    intro r row
    simp [Table.visible, h]
  refine ⟨?_, ?_⟩
  · rintro row ⟨r, hr⟩
    rw [hvis r row] at hr
    exact Bool.noConfusion hr
  · intro r
    simp [Table.select, hvis r]

/-- Non-vacuity check: with RLS switched on and no policies attached, every row of the
table *is* protected.  So the hypothesis `rlsEnabled = false` above is doing real work. -/
theorem rls_on_no_policies_protects (t : Table Row) (h : t.rlsEnabled = true)
    (hp : t.policies = []) : ∀ row : Row, t.IsProtected row := by
  intro row
  exact ⟨"anyone", by simp [Table.visible, h, hp]⟩

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

