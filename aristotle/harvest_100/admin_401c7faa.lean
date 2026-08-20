/-
# Pauli Exclusion Antisym
Category: Quantum Physics
Target: QPhys.pauli_exclusion_antisym
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace QPhys

open TensorProduct

/-- The (unnormalized) two-fermion Slater state built from single-particle states
`psi` and `chi`: the antisymmetrization `psi ⊗ chi - chi ⊗ psi` inside the two-particle
Hilbert space `V ⊗ V`. -/
noncomputable def slater2 {𝕜 V : Type*} [CommRing 𝕜] [AddCommGroup V] [Module 𝕜 V]
    (psi chi : V) : TensorProduct 𝕜 V V :=
  psi ⊗ₜ[𝕜] chi - chi ⊗ₜ[𝕜] psi

/-- The two-fermion Slater state is antisymmetric under exchange of the two
single-particle states. -/
theorem slater2_swap {𝕜 V : Type*} [CommRing 𝕜] [AddCommGroup V] [Module 𝕜 V]
    (psi chi : V) : slater2 (𝕜 := 𝕜) chi psi = - slater2 (𝕜 := 𝕜) psi chi := by
  simp [slater2]

/-- **Pauli exclusion principle (antisymmetry form).**
A two-fermion antisymmetric state with equal single-particle states is zero:
the antisymmetrized state `psi ⊗ psi - psi ⊗ psi` vanishes, and more generally any
exchange-antisymmetric two-particle wave function `Psi` (valued in a complex
vector space) vanishes on the diagonal. -/
theorem pauli_exclusion_antisym {𝕜 V : Type*} [CommRing 𝕜] [AddCommGroup V] [Module 𝕜 V]
    {W : Type*} [AddCommGroup W] [Module ℂ W]
    (psi : V) (Psi : V → V → W) (hPsi : ∀ x y : V, Psi x y = - Psi y x) :
    slater2 (𝕜 := 𝕜) psi psi = 0 ∧ Psi psi psi = 0 := by
  refine ⟨?_, ?_⟩
  · simp [slater2]
  · have h : Psi psi psi = - Psi psi psi := hPsi psi psi
    have h2 : (2 : ℂ) • Psi psi psi = 0 := by
      rw [two_smul]
      nth_rewrite 1 [h]
      simp
    have := congrArg (fun w : W => (2 : ℂ)⁻¹ • w) h2
    simpa [smul_smul] using this

end QPhys

