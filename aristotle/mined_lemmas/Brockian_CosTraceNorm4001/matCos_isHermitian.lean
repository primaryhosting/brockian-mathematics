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

lemma matCos_isHermitian {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    (matCos A).IsHermitian := by
  unfold Matrix.IsHermitian matCos
  rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_add, conjTranspose_exp_I_smul hA,
    conjTranspose_exp_neg_I_smul hA]
  rw [add_comm]
  norm_num

