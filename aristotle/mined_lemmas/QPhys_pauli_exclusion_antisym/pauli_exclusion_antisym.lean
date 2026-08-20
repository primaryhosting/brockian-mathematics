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
