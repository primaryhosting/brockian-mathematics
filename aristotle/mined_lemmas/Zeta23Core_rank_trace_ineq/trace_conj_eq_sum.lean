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

theorem trace_conj_eq_sum (Pr A : Matrix n n 𝕜) (hPr : Prᴴ = Pr) :
    Matrix.trace (Pr * A * Pr)
      = ∑ a, (star (fun b => Pr b a) ⬝ᵥ (A *ᵥ (fun b => Pr b a))) := by
  have hb : ∀ a b, Pr a b = star (Pr b a) := by
    intro a b; conv_lhs => rw [← hPr]
    simp [Matrix.conjTranspose_apply]
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, dotProduct, Matrix.mulVec,
    Pi.star_apply, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ => ?_
  rw [hb a b]
  ring

/-- For an idempotent Hermitian `Pr`, the real part of `tr (Pr * A)` is the sum of the
quadratic form of `A` over the columns of `Pr`. -/
