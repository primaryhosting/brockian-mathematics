import Mathlib

/-!
# Cos Trace Norm 4001
Category: Brockian Corpus
Target: Brockian.CosTraceNorm4001
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (Lean 4 requires `import` lines to precede any module doc comment, so the header
-- block above sits immediately after the single `import Mathlib` line.)

open scoped BigOperators
open scoped Real
open scoped Matrix

set_option maxRecDepth 10000

namespace Brockian

/-- The cosine kernel matrix `C i j = cos (x i - x j)` attached to a family of phases `x`. -/

theorem cos_kernel_trace (n : ℕ) (x : Fin n → ℝ) : (cosKernel n x).trace = n := by
  simp [Matrix.trace, Matrix.diag, cosKernel]

/-- Since the cosine kernel is positive semidefinite with trace `n`, its trace norm is `n`, and
hence its quadratic form is bounded by `n * ‖v‖²`. -/
