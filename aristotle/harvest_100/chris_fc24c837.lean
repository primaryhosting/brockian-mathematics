/-
# Cos Trace Norm 4001
Category: Brockian Corpus
Target: Brockian.CosTraceNorm4001
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Brockian

/-- **Cos trace norm bound.**  For any phases `θ : Fin 4001 → ℝ` and any real
`4001 × 4001` matrix `A`, the trace of `diagonal (cos ∘ θ) * A` is bounded in
absolute value by the sum of the absolute values of the diagonal entries of `A`.
In particular, taking `A = 1`, one gets `|∑ i, cos (θ i)| ≤ 4001`. -/
theorem CosTraceNorm4001 (θ : Fin 4001 → ℝ) (A : Matrix (Fin 4001) (Fin 4001) ℝ) :
    |Matrix.trace (Matrix.diagonal (fun i => Real.cos (θ i)) * A)| ≤ ∑ i, |A i i| := by
  have htr : Matrix.trace (Matrix.diagonal (fun i => Real.cos (θ i)) * A)
      = ∑ i, Real.cos (θ i) * A i i := by
    simp [Matrix.trace, Matrix.diag, Matrix.diagonal_mul]
  rw [htr]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  refine Finset.sum_le_sum ?_
  intro i _
  rw [abs_mul]
  exact mul_le_of_le_one_left (abs_nonneg _) (Real.abs_cos_le_one _)

/-- Specialising `CosTraceNorm4001` to `A = 1` : the sum of 4001 cosines is at most 4001 in
absolute value. -/
theorem CosTraceNorm4001_one (θ : Fin 4001 → ℝ) :
    |∑ i, Real.cos (θ i)| ≤ 4001 := by
  have h := CosTraceNorm4001 θ 1
  simpa using h

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

