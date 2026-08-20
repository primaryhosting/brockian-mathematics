import Mathlib

/-!
# Rank Trace Ineq
Category: Brockian Corpus
Target: Zeta23Core.rank_trace_ineq
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped ComplexOrder
open Matrix

set_option maxHeartbeats 1000000

namespace Zeta23Core

variable {n : Type*} [Fintype n] {𝕜 : Type*} [RCLike 𝕜]

/-- The squared Frobenius norm of a matrix: `‖M‖_F² = Re tr(Mᴴ M)`. -/

theorem indicator_proj_annihilates [DecidableEq n] {B U2 : Matrix n n 𝕜} (mu : n → ℝ) (hU2 : U2ᴴ * U2 = 1)
    (h : B * (U2 * diagonal (RCLike.ofReal ∘ mu) * U2ᴴ) = 0) :
    B * (U2 * diagonal (fun i => if mu i ≠ 0 then (1:𝕜) else 0) * U2ᴴ) = 0 := by
  have h1 : (B * U2) * diagonal (RCLike.ofReal ∘ mu) = 0 := by
    have h2 := congrArg (fun X => X * U2) h
    simp only [Matrix.mul_assoc, Matrix.zero_mul, hU2, Matrix.mul_one] at h2
    simpa [Matrix.mul_assoc] using h2
  have h3 : (B * U2) * diagonal (fun i => if mu i ≠ 0 then (1:𝕜) else 0) = 0 := by
    ext a i
    have hai := congrFun (congrFun h1 a) i
    simp only [Matrix.mul_diagonal, Matrix.zero_apply, Function.comp] at hai ⊢
    by_cases hm : mu i = 0
    · simp [hm]
    · have hB : (B * U2) a i = 0 := by
        rcases mul_eq_zero.mp hai with h' | h'
        · exact h'
        · exact absurd h' (by simpa using hm)
      simp [hm, hB]
  calc B * (U2 * diagonal (fun i => if mu i ≠ 0 then (1:𝕜) else 0) * U2ᴴ)
      = ((B * U2) * diagonal (fun i => if mu i ≠ 0 then (1:𝕜) else 0)) * U2ᴴ := by
        simp [Matrix.mul_assoc]
    _ = 0 := by rw [h3, Matrix.zero_mul]

/-- A Hermitian projection acting as the identity on `M Mᴴ` acts as the identity on `M`. -/
