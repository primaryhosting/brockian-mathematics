import Mathlib

/-!
# A trace-norm bound for the matrix cosine

For a Hermitian complex matrix `A` we define the matrix cosine and sine by

  `cos A = (exp (I • A) + exp (-(I • A))) / 2`,  `sin A = (exp (I • A) - exp (-(I • A))) / (2 I)`,

and the trace norm (nuclear norm) of a matrix `M` as the sum of its singular values, i.e.
the sum of the square roots of the eigenvalues of `Mᴴ * M`.

The main result `Brockian.CosTraceNorm4001` states `‖cos A‖₁ ≤ card n`.
-/

namespace Brockian

open Matrix
open scoped ComplexOrder

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The trace norm (nuclear norm) of a complex matrix: the sum of its singular values,
i.e. the sum of the square roots of the eigenvalues of `Mᴴ * M`. -/

lemma exp_neg_mul_exp (A : Matrix n n ℂ) :
    NormedSpace.exp (-(Complex.I • A)) * NormedSpace.exp (Complex.I • A) = 1 := by
  have hc : Commute (-(Complex.I • A)) (Complex.I • A) := (Commute.refl _).neg_left
  rw [← Matrix.exp_add_of_commute _ _ hc, neg_add_cancel, NormedSpace.exp_zero]

