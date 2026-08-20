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
# Pure State Zero Entropy
Category: Quantum Computing
Target: QC.pure_state_zero_entropy
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Pure State Zero Entropy
Category: Quantum Computing
Target: QC.pure_state_zero_entropy
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open Matrix

namespace QC

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The von Neumann entropy `S(ρ) = -Tr(ρ log ρ)` of a Hermitian (density) matrix `ρ`,
computed in the eigenbasis: `S(ρ) = ∑ i, -λ i * log (λ i)` where `λ` are the eigenvalues
of `ρ`. -/

theorem IsPureState.mul_self {ρ : Matrix n n ℂ} (h : IsPureState ρ) : ρ * ρ = ρ := by
  obtain ⟨ψ, hψ, rfl⟩ := h
  have hsum : ∑ k, (starRingEnd ℂ) (ψ k) * ψ k = 1 := by
    have h1 : ∑ k, (starRingEnd ℂ) (ψ k) * ψ k = ((∑ k, ‖ψ k‖ ^ 2 : ℝ) : ℂ) := by
      push_cast
      exact Finset.sum_congr rfl fun k _ => Complex.conj_mul' (ψ k)
    rw [h1, hψ, Complex.ofReal_one]
  ext i j
  simp only [Matrix.mul_apply, Matrix.vecMulVec_apply, Pi.star_apply, RCLike.star_def]
  calc ∑ k, ψ i * (starRingEnd ℂ) (ψ k) * (ψ k * (starRingEnd ℂ) (ψ j))
      = (ψ i * (starRingEnd ℂ) (ψ j)) * ∑ k, (starRingEnd ℂ) (ψ k) * ψ k := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring
    _ = ψ i * (starRingEnd ℂ) (ψ j) := by rw [hsum, mul_one]

/-- Eigenvalues of a Hermitian idempotent matrix are `0` or `1`. -/
