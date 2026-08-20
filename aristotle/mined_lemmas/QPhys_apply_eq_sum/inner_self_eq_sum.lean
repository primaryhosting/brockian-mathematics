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
# Variational Bound
Category: Quantum Physics
Target: QPhys.variational_bound
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace QPhys

open scoped InnerProductSpace

variable {n : ℕ} {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

/-- Expansion of `H ψ` in an orthonormal eigenbasis of `H`. -/

lemma inner_self_eq_sum (b : OrthonormalBasis (Fin n) ℂ V) (psi : V) :
    ⟪psi, psi⟫_ℂ = ((∑ i, ‖⟪b i, psi⟫_ℂ‖ ^ 2 : ℝ) : ℂ) := by
  rw [← b.sum_inner_mul_inner psi psi]
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← inner_conj_symm (b i) psi]
  rw [show ⟪psi, b i⟫_ℂ * (starRingEnd ℂ) ⟪psi, b i⟫_ℂ
      = (1 : ℂ) * (⟪psi, b i⟫_ℂ * (starRingEnd ℂ) ⟪psi, b i⟫_ℂ) by ring,
    Complex.mul_conj]
  simp [Complex.normSq_eq_norm_sq, norm_inner_symm]

/-- The expectation value `⟨ψ|H|ψ⟩` is the eigenvalue-weighted sum `∑ᵢ μᵢ |cᵢ|²`. -/
