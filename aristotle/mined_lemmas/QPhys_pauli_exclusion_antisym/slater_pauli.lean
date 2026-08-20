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

