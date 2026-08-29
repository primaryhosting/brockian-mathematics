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

theorem norm_trace_le_traceNorm_of_conjTranspose_mul_self_eq_one {n : Type*} [Fintype n]
    [DecidableEq n] (A : Matrix n n ℂ) (h : Aᴴ * A = 1) : ‖A.trace‖ ≤ traceNorm A := by
  rw [traceNorm_of_conjTranspose_mul_self_eq_one A h, Matrix.trace]
  calc ‖∑ i, A.diag i‖ ≤ ∑ i, ‖A.diag i‖ := norm_sum_le _ _
    _ ≤ ∑ _i : n, (1 : ℝ) :=
        Finset.sum_le_sum fun i _ => norm_diag_le_one_of_conjTranspose_mul_self_eq_one A h i
    _ = Fintype.card n := by simp

/-- The `2 × 2` rotation matrix by angle `θ`, viewed as a complex matrix. -/
