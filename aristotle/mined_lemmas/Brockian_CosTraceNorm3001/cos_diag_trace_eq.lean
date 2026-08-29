/-
# Cos Trace Norm 3001
Category: Brockian Corpus
Target: Brockian.CosTraceNorm3001
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (The header above uses `/- -/` rather than `/-! -/` because Lean 4 does not permit a
-- module doc comment to precede the `import` commands; the text is otherwise verbatim.)

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Brockian

/-- Trace of a cosine-phase diagonal matrix times an arbitrary matrix:
`Tr (diag (cos θ) * A) = ∑ i, cos (θ i) * A i i`.

This is the basic computation underlying the `CosTraceNorm` family; it follows from
`Matrix.diagonal_mul` together with the definition of `Matrix.trace`. -/

theorem cos_diag_trace_eq {n : Type*} [Fintype n] [DecidableEq n]
    (θ : n → ℝ) (A : Matrix n n ℝ) :
    Matrix.trace (Matrix.diagonal (fun i => Real.cos (θ i)) * A)
      = ∑ i, Real.cos (θ i) * A i i := by
  simp [Matrix.trace, Matrix.diagonal_mul, Matrix.diag]

/-- **Refined cosine trace bound.**  For every phase vector `θ` and every matrix `A`,
`|Tr (diag (cos θ) * A)| ≤ ∑ i, |cos (θ i)| * |A i i|`.

The key Mathlib ingredient is `Finset.abs_sum_le_sum_abs`, the triangle inequality for
finite sums. -/
