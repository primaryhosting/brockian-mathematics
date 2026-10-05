import Mathlib

/-!
# Rank Trace Ineq
Category: Brockian Corpus
Target: Zeta23Core.rank_trace_ineq
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise
open scoped ComplexOrder

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 40000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Zeta23Core

open Matrix

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-! ## Basic definitions -/

/-- The squared Frobenius norm of a matrix, `‖M‖_F² = Re tr (Mᴴ M)`. -/

lemma re_trace_mul_nonneg {P₁ P₂ : Matrix n n 𝕜} (h₁ : P₁.PosSemidef) (h₂ : P₂.PosSemidef) :
    0 ≤ RCLike.re (Matrix.trace (P₁ * P₂)) := by
  obtain ⟨T, hTpsd, hTT⟩ : ∃ T : Matrix n n 𝕜, T.PosSemidef ∧ T * T = P₁ := by
    refine ⟨hFun h₁.1 Real.sqrt, hFun_posSemidef h₁.1 fun i => Real.sqrt_nonneg _, ?_⟩
    rw [hFun_mul, show (hFun h₁.1 fun x => Real.sqrt x * Real.sqrt x) = hFun h₁.1 (fun x => x) from
      hFun_congr h₁.1 fun i => Real.mul_self_sqrt (h₁.eigenvalues_nonneg i), hFun_id]
  have hTH : Tᴴ = T := hTpsd.1
  have key : Matrix.trace (P₁ * P₂) = Matrix.trace (Tᴴ * P₂ * T) := by
    rw [hTH, ← hTT, Matrix.mul_assoc, Matrix.trace_mul_comm T (T * P₂), Matrix.mul_assoc]
  rw [key]
  simpa using RCLike.re_le_re (h₂.conjTranspose_mul_mul_same T).trace_nonneg

omit [DecidableEq n] in
/-- A Hermitian idempotent matrix is positive semidefinite. -/
