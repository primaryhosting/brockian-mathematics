/-
# Pauli Exclusion Antisym
Category: Quantum Physics
Target: QPhys.pauli_exclusion_antisym
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace QPhys

open TensorProduct

variable {H : Type*} [AddCommGroup H] [Module ℂ H]

/-- The antisymmetrized (fermionic) two-particle state built from single-particle
states `u` and `v`: `u ⊗ v - v ⊗ u`. -/
noncomputable def antisymState (u v : H) : H ⊗[ℂ] H := u ⊗ₜ[ℂ] v - v ⊗ₜ[ℂ] u

/-- **Pauli exclusion principle.** A two-fermion state `Ψ` in `H ⊗ H` which is
antisymmetric under exchange of the two particles and which is the product state
`ψ ⊗ ψ` of two *equal* single-particle states is necessarily the zero state. -/
theorem pauli_exclusion_antisym (ψ : H) (Ψ : H ⊗[ℂ] H) (hΨ : Ψ = ψ ⊗ₜ[ℂ] ψ)
    (hanti : TensorProduct.comm ℂ H H Ψ = -Ψ) :
    Ψ = 0 := by
  subst hΨ
  simp only [TensorProduct.comm_tmul] at hanti
  -- `hanti : ψ ⊗ ψ = -(ψ ⊗ ψ)`, hence `(2 : ℂ) • (ψ ⊗ ψ) = 0`
  have h2 : (2 : ℂ) • (ψ ⊗ₜ[ℂ] ψ) = 0 := by
    rw [two_smul, ← eq_neg_iff_add_eq_zero]
    exact hanti
  rcases smul_eq_zero.mp h2 with h | h
  · exact absurd h (by norm_num)
  · exact h

/-- The antisymmetrized state formed from two equal single-particle states vanishes. -/
theorem antisymState_self (ψ : H) : antisymState ψ ψ = 0 := sub_self _

/-- The antisymmetrized state is indeed antisymmetric under particle exchange. -/
theorem comm_antisymState (u v : H) :
    TensorProduct.comm ℂ H H (antisymState u v) = -antisymState u v := by
  simp [antisymState, neg_sub]

/-- Exterior-algebra form of the exclusion principle: the wedge of a single-particle
state with itself is zero (`ExteriorAlgebra.ι_sq_zero`). -/
theorem wedge_self_eq_zero (ψ : H) :
    ExteriorAlgebra.ι ℂ ψ * ExteriorAlgebra.ι ℂ ψ = 0 :=
  ExteriorAlgebra.ι_sq_zero ψ

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

