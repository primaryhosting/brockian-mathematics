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

theorem proj_mul_eq_self {Pr M : Matrix n n 𝕜} (hPrh : Prᴴ = Pr)
    (hG : Pr * (M * Mᴴ) = M * Mᴴ) : Pr * M = M := by
  have hGPr : (M * Mᴴ) * Pr = M * Mᴴ := by
    have := congrArg Matrix.conjTranspose hG
    simpa [Matrix.conjTranspose_mul, hPrh, Matrix.mul_assoc] using this
  have key : (Pr * M - M) * (Pr * M - M)ᴴ = 0 := by
    have e1 : (Pr * M - M)ᴴ = Mᴴ * Pr - Mᴴ := by
      simp [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, hPrh]
    rw [e1, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub]
    have a1 : Pr * M * (Mᴴ * Pr) = M * Mᴴ := by
      rw [← Matrix.mul_assoc, Matrix.mul_assoc Pr M Mᴴ, hG, hGPr]
    have a2 : Pr * M * Mᴴ = M * Mᴴ := by rw [Matrix.mul_assoc, hG]
    have a3 : M * (Mᴴ * Pr) = M * Mᴴ := by rw [← Matrix.mul_assoc, hGPr]
    rw [a1, a2, a3]
    abel
  exact sub_eq_zero.mp (Matrix.self_mul_conjTranspose_eq_zero.mp key)

/-! ### The rank–trace inequality -/

/-- **Rank–trace inequality** (Lemma 3.2 of the preprint).

Let `P` be a positive semidefinite `n × n` matrix over an `RCLike` field with `rank P ≤ r`,
let `Q` be Hermitian with at most `b` positive eigenvalues (`posIndex Q ≤ b`), and let `c > 0`
be a real number.  Then
`c·Re tr P − (c²/4)·r + 2c·Re tr Q − c²·b ≤ ‖P + Q‖_F²`. -/
