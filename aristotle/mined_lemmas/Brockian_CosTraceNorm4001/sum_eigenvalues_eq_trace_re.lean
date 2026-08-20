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

lemma sum_eigenvalues_eq_trace_re {M : Matrix n n ℂ} (hM : M.IsHermitian) :
    ∑ i, hM.eigenvalues i = (Matrix.trace M).re := by
  rw [hM.trace_eq_sum_eigenvalues]
  rw [Complex.re_sum]
  simp

/-- **A trace-norm bound for the matrix cosine.**  For a Hermitian matrix `A`, the trace norm
(sum of singular values) of `cos A` is at most the dimension. -/
