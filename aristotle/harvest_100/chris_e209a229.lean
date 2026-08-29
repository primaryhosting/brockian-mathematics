/-
# Pauli Exclusion Antisym
Category: Quantum Physics
Target: QPhys.pauli_exclusion_antisym
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (Lean requires `import` commands to precede any module docstring, so the header
-- above is written as a plain block comment and repeated as a module docstring below.)

import Mathlib

/-!
# Pauli Exclusion Antisym
Category: Quantum Physics
Target: QPhys.pauli_exclusion_antisym
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QPhys

open scoped TensorProduct

/-- The antisymmetrized (Slater) two-particle state built from two single-particle
states `psi` and `phi` of a complex vector space `V`:
`slater2 psi phi = psi ⊗ phi - phi ⊗ psi ∈ V ⊗ V`. -/
noncomputable def slater2 {V : Type*} [AddCommGroup V] [Module ℂ V] (psi phi : V) : V ⊗[ℂ] V :=
  psi ⊗ₜ[ℂ] phi - phi ⊗ₜ[ℂ] psi

/-- **Pauli exclusion principle (antisymmetry form).**
A two-fermion state `Ψ`, valued in a complex vector space and antisymmetric under
exchange of the two particle labels (`Ψ x y = - Ψ y x`), vanishes when both fermions
occupy the same single-particle state `x`. -/
theorem pauli_exclusion_antisym {ι : Type*} {M : Type*} [AddCommGroup M] [Module ℂ M]
    (Ψ : ι → ι → M) (hanti : ∀ x y, Ψ x y = - Ψ y x) (x : ι) :
    Ψ x x = 0 := by
  have h : Ψ x x = - Ψ x x := hanti x x
  have h2 : (2 : ℂ) • Ψ x x = 0 := by
    rw [two_smul]
    nth_rewrite 2 [h]
    simp
  rcases smul_eq_zero.mp h2 with h0 | h0
  · exact absurd h0 (by norm_num)
  · exact h0

/-- Scalar (wavefunction) form of the Pauli exclusion principle: an antisymmetric
two-particle wavefunction has zero amplitude on coinciding single-particle states. -/
theorem pauli_exclusion_wavefunction {ι : Type*} (Ψ : ι → ι → ℂ)
    (hanti : ∀ x y, Ψ x y = - Ψ y x) (x : ι) :
    Ψ x x = 0 :=
  pauli_exclusion_antisym Ψ hanti x

/-- The Slater two-particle state is antisymmetric under exchange of the two particles. -/
theorem slater2_antisymm {V : Type*} [AddCommGroup V] [Module ℂ V] (psi phi : V) :
    slater2 psi phi = - slater2 phi psi := by
  simp [slater2]

/-- The Slater determinant state of two fermions occupying the *same* single-particle
state vanishes: two identical fermions cannot occupy the same state. -/
theorem slater2_self_eq_zero {V : Type*} [AddCommGroup V] [Module ℂ V] (psi : V) :
    slater2 psi psi = 0 :=
  pauli_exclusion_antisym (M := V ⊗[ℂ] V) slater2 slater2_antisymm psi

end QPhys

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

