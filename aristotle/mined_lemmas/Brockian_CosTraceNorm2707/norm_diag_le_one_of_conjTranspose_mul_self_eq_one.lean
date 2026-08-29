/-
# Cos Trace Norm 2707
Category: Brockian Corpus
Target: Brockian.CosTraceNorm2707
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (The header above is a plain comment because Lean requires `import` to precede any
-- module docstring; the identical header is repeated as the module docstring below.)

import Mathlib

/-!
# Cos Trace Norm 2707
Category: Brockian Corpus
Target: Brockian.CosTraceNorm2707
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Matrix
open scoped MatrixOrder

namespace Brockian

/-- The trace norm (Schatten 1-norm) of a complex square matrix `A`:
the trace of the positive semidefinite square root of `Aᴴ * A`,
i.e. the sum of the singular values of `A`. -/

theorem norm_diag_le_one_of_conjTranspose_mul_self_eq_one {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) (h : Aᴴ * A = 1) (i : n) : ‖A i i‖ ≤ 1 := by
  have h1 : ∑ k, ‖A k i‖ ^ 2 = 1 := by
    have hd := congrArg (fun M => M i i) h
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply_eq] at hd
    have h2 : ((∑ k, ‖A k i‖ ^ 2 : ℝ) : ℂ) = 1 := by
      push_cast
      rw [← hd]
      refine Finset.sum_congr rfl fun k _ => ?_
      simpa [mul_comm] using (Complex.mul_conj' (A k i)).symm
    exact_mod_cast h2
  have hle := Finset.single_le_sum (f := fun k => ‖A k i‖ ^ 2) (fun k _ => sq_nonneg _)
    (Finset.mem_univ i)
  rw [h1] at hle
  nlinarith [norm_nonneg (A i i)]

/-- The trace-norm bound `|tr A| ≤ ‖A‖₁` for matrices with orthonormal columns. -/
