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

/-
# Ramsey 3 5
Category: Pure Mathematics
Target: Math.ramsey_3_5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Ramsey 3 5
Category: Pure Mathematics
Target: Math.ramsey_3_5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-! ## Relative (Finset-localized) triangles and independent sets -/

section Rel

variable {V : Type*} [LinearOrder V]

/-- `t` is an independent set of `G`. -/

def RamseyProp (n : ℕ) : Prop :=
  ∀ G : SimpleGraph (Fin n),
    (∃ s : Finset (Fin n), s.card = 3 ∧ ∀ x ∈ s, ∀ y ∈ s, x ≠ y → G.Adj x y) ∨
    (∃ s : Finset (Fin n), s.card = 5 ∧ ∀ x ∈ s, ∀ y ∈ s, x ≠ y → ¬ G.Adj x y)

