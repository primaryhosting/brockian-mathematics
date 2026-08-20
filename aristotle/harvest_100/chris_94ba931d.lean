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

/-- The (unnormalized) two-fermion Slater state built from two single-particle
states `ψ` and `χ`: the antisymmetrized tensor product `ψ ⊗ χ - χ ⊗ ψ`. -/
noncomputable def slater {H : Type*} [AddCommGroup H] [Module ℂ H] (ψ χ : H) :
    TensorProduct ℂ H H :=
  ψ ⊗ₜ[ℂ] χ - χ ⊗ₜ[ℂ] ψ

/-- The Slater state is antisymmetric under exchange of the two particles. -/
theorem slater_antisymm {H : Type*} [AddCommGroup H] [Module ℂ H] (ψ χ : H) :
    slater ψ χ = - slater χ ψ := by
  simp [slater]

/-- **Pauli exclusion principle (antisymmetry form).**

Any antisymmetric two-particle state vanishes when the two single-particle states
coincide.  Concretely, if `Ψ` is a `ℂ`-bilinear two-particle amplitude (valued in an
arbitrary complex vector space `W`, so this covers both scalar wavefunctions and
tensor-product-valued states) which is antisymmetric under exchange of the two
particles, then `Ψ ψ ψ = 0` for every single-particle state `ψ`. -/
theorem pauli_exclusion_antisym {H W : Type*} [AddCommGroup H] [Module ℂ H]
    [AddCommGroup W] [Module ℂ W] (Ψ : H →ₗ[ℂ] H →ₗ[ℂ] W)
    (hΨ : ∀ x y : H, Ψ x y = - Ψ y x) (ψ : H) :
    Ψ ψ ψ = 0 := by
  have h : Ψ ψ ψ = - Ψ ψ ψ := hΨ ψ ψ
  have h2 : (2 : ℂ) • Ψ ψ ψ = 0 := by
    rw [two_smul]
    nth_rewrite 1 [h]
    simp
  have := congrArg (fun v => (2 : ℂ)⁻¹ • v) h2
  simpa [smul_smul] using this

/-- Specialization: the two-fermion Slater state with equal single-particle states
is the zero state. -/
theorem slater_self_eq_zero {H : Type*} [AddCommGroup H] [Module ℂ H] (ψ : H) :
    slater ψ ψ = 0 := by
  simp [slater]

/-- The Slater construction, viewed as a bilinear map, is antisymmetric, hence the
Pauli exclusion theorem applies to it and forces `slater ψ ψ = 0`. -/
theorem slater_pauli {H : Type*} [AddCommGroup H] [Module ℂ H] (ψ : H) :
    slater ψ ψ = 0 := by
  let B : H →ₗ[ℂ] H →ₗ[ℂ] TensorProduct ℂ H H :=
    (TensorProduct.mk ℂ H H) - (TensorProduct.mk ℂ H H).flip
  have hB : ∀ x y : H, B x y = - B y x := by
    intro x y
    simp [B, sub_eq_add_neg, add_comm]
  have h := pauli_exclusion_antisym B hB ψ
  show B ψ ψ = 0
  exact h

end QPhys

