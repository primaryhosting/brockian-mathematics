/-
# Cos Trace Norm 3499
Category: Brockian Corpus
Target: Brockian.CosTraceNorm3499
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Cos Trace Norm 3499
Category: Brockian Corpus
Target: Brockian.CosTraceNorm3499
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian

/-- **Cos trace norm bound.** For any family of angles `θ : n → ℝ` indexed by a finite type,
the absolute value of the trace of the diagonal matrix with entries `cos (θ i)` is bounded by
the cardinality of the index type.

The proof combines `Matrix.trace_diagonal`, the triangle inequality
`Finset.abs_sum_le_sum_abs`, and the pointwise bound `Real.abs_cos_le_one`. -/
theorem CosTraceNorm3499 {n : Type*} [Fintype n] [DecidableEq n] (θ : n → ℝ) :
    |Matrix.trace (Matrix.diagonal (fun i => Real.cos (θ i)))| ≤ (Fintype.card n : ℝ) := by
  rw [Matrix.trace_diagonal]
  calc |∑ i, Real.cos (θ i)|
      ≤ ∑ i, |Real.cos (θ i)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : n, (1 : ℝ) := Finset.sum_le_sum fun i _ => Real.abs_cos_le_one _
    _ = (Fintype.card n : ℝ) := by simp [Finset.card_univ]

/-- **Sharper form.** The trace of the diagonal cosine matrix is bounded in absolute value by
the trace of the diagonal matrix of the absolute values `|cos (θ i)|`, i.e. by the trace norm
(sum of singular values) of that Hermitian diagonal matrix. -/
theorem CosTraceNorm3499_le_traceAbs {n : Type*} [Fintype n] [DecidableEq n] (θ : n → ℝ) :
    |Matrix.trace (Matrix.diagonal (fun i => Real.cos (θ i)))|
      ≤ Matrix.trace (Matrix.diagonal (fun i => |Real.cos (θ i)|)) := by
  rw [Matrix.trace_diagonal, Matrix.trace_diagonal]
  exact Finset.abs_sum_le_sum_abs _ _

/-- **Sharpness.** The bound `Fintype.card n` in `CosTraceNorm3499` is attained, e.g. for the
zero family of angles. -/
theorem CosTraceNorm3499_isSharp {n : Type*} [Fintype n] [DecidableEq n] :
    Matrix.trace (Matrix.diagonal (fun _ : n => Real.cos (0 : ℝ))) = (Fintype.card n : ℝ) := by
  simp

end Brockian

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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

