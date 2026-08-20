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

lemma matCos_zero : matCos (0 : Matrix n n ℂ) = 1 := by
  rw [matCos]
  simp only [smul_zero, neg_zero, NormedSpace.exp_zero]
  module

/-- The bound in `CosTraceNorm4001` is sharp: it is attained at `A = 0`. -/
