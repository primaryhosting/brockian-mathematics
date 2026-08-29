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

