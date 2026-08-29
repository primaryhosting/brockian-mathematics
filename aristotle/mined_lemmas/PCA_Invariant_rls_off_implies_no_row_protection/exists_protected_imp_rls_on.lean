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

/-!
# Rls Off Implies No Row Protection
Category: Proof-Carrying Apps
Target: PCA.Invariant.rls_off_implies_no_row_protection
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace PCA.Invariant

universe u v

/-- A row-level-security policy: it says which principals may see which rows. -/
structure Policy (Row : Type u) (Principal : Type v) where
  /-- `permits p r` holds when the policy grants principal `p` access to row `r`. -/
  permits : Principal → Row → Prop

/-- A table of the isolation engine's model: a row-level-security switch
together with the policies that are installed on the table. -/
structure Table (Row : Type u) (Principal : Type v) where
  /-- Whether row-level security is switched on for this table. -/
  rlsEnabled : Bool
  /-- The policies installed on the table. -/
  policies : List (Policy Row Principal)

variable {Row : Type u} {Principal : Type v}

/-- The visibility semantics of the engine: when row-level security is off every
row is visible to every principal; when it is on, a row is visible to a principal
exactly when some installed policy permits it. -/

theorem exists_protected_imp_rls_on
    (t : Table Row Principal) (h : ∃ r : Row, RowProtected t r) :
    t.rlsEnabled = true := by
  obtain ⟨r, hr⟩ := h
  cases hb : t.rlsEnabled with
  | false => exact absurd hr (rls_off_implies_no_row_protection t hb r)
  | true => rfl

end PCA.Invariant

