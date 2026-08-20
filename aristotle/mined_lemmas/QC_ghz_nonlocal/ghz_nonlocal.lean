/-
# Ghz Nonlocal
Category: Quantum Computing
Target: QC.ghz_nonlocal
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace QC

open Matrix Complex
open scoped Kronecker

/-- The Pauli `X` matrix. -/

theorem ghz_nonlocal :
    (ghz ≠ 0 ∧
     (op3 pauliX pauliY pauliY) *ᵥ ghz = -ghz ∧
     (op3 pauliY pauliX pauliY) *ᵥ ghz = -ghz ∧
     (op3 pauliY pauliY pauliX) *ᵥ ghz = -ghz ∧
     (op3 pauliX pauliX pauliX) *ᵥ ghz = ghz) ∧
    ∀ x y : Fin 3 → ℤ, (∀ i, x i = 1 ∨ x i = -1) → (∀ i, y i = 1 ∨ y i = -1) →
      ¬ (x 0 * y 1 * y 2 = -1 ∧ y 0 * x 1 * y 2 = -1 ∧ y 0 * y 1 * x 2 = -1 ∧
         x 0 * x 1 * x 2 = 1) :=
  ⟨⟨ghz_ne_zero, ghz_XYY, ghz_YXY, ghz_YYX, ghz_XXX⟩, no_local_hidden_variables⟩

end QC
#print axioms QC.ghz_nonlocal

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

