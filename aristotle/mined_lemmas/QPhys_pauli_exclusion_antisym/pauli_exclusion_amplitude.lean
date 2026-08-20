import Mathlib

/-!
# Pauli Exclusion Antisym
Category: Quantum Physics
Target: QPhys.pauli_exclusion_antisym
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/


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

namespace QPhys

variable {𝕜 H : Type*} [CommRing 𝕜] [AddCommGroup H] [Module 𝕜 H]

/-- The antisymmetrized (unnormalized) two-particle state built from single-particle
states `u` and `v`: the Slater-determinant combination `u ⊗ v - v ⊗ u`. -/

theorem pauli_exclusion_amplitude {ι : Type*} (Psi : ι → ι → ℂ)
    (hPsi : ∀ i j, Psi i j = -Psi j i) (i : ι) : Psi i i = 0 := by
  have h := hPsi i i
  linear_combination h / 2

end QPhys

