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
open scoped TensorProduct

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

/-- **Pauli exclusion principle (antisymmetry form).**

A two-fermion wavefunction is an amplitude `Ψ : H → H → W` assigning to a pair of
single-particle configurations `a b : H` an amplitude in a complex vector space `W`
(typically `W = ℂ`), subject to the fermionic antisymmetry law `Ψ a b = - Ψ b a`.

Then the amplitude for the two fermions occupying the *same* single-particle state
vanishes: `Ψ a a = 0`. -/
theorem pauli_exclusion_antisym {H W : Type*} [AddCommGroup W] [Module ℂ W]
    (Ψ : H → H → W) (hΨ : ∀ a b : H, Ψ a b = -Ψ b a) (a : H) :
    Ψ a a = 0 := by
  have hself : Ψ a a + Ψ a a = 0 := by
    rw [add_eq_zero_iff_eq_neg]
    exact hΨ a a
  have h2 : (2 : ℂ) • Ψ a a = 0 := by
    rw [two_smul]
    exact hself
  rcases smul_eq_zero.mp h2 with h | h
  · exact absurd h two_ne_zero
  · exact h

/-- The antisymmetrized (Slater determinant) two-particle state built from two
single-particle states `u v` of a complex Hilbert space `H`. -/
noncomputable def slater {H : Type*} [AddCommGroup H] [Module ℂ H] (u v : H) :
    H ⊗[ℂ] H :=
  u ⊗ₜ[ℂ] v - v ⊗ₜ[ℂ] u

/-- `slater` is antisymmetric under exchange of the two single-particle states. -/
theorem slater_antisymm {H : Type*} [AddCommGroup H] [Module ℂ H] (u v : H) :
    slater u v = -slater v u := by
  simp [slater]

/-- **Pauli exclusion for the Slater state**: the antisymmetric two-fermion state
formed from two *equal* single-particle states is the zero vector. -/
theorem slater_self_eq_zero {H : Type*} [AddCommGroup H] [Module ℂ H] (u : H) :
    slater u u = 0 :=
  pauli_exclusion_antisym slater slater_antisymm u

end QPhys

