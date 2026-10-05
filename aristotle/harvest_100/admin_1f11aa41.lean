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

/-- **Cos trace norm bound.**  For any family of angles `θ : Fin n → ℝ`, the trace of the
diagonal matrix with entries `cos (θ i)` has absolute value at most `n`.

The proof rewrites the trace of a diagonal matrix as the sum of its diagonal entries
(`Matrix.trace_diagonal`), then applies the triangle inequality for finite sums
(`Finset.abs_sum_le_sum_abs`) together with `Real.abs_cos_le_one`. -/
theorem CosTraceNorm3499 (n : ℕ) (θ : Fin n → ℝ) :
    |(Matrix.diagonal (fun i => Real.cos (θ i))).trace| ≤ (n : ℝ) := by
  rw [Matrix.trace_diagonal]
  calc |∑ i, Real.cos (θ i)| ≤ ∑ i, |Real.cos (θ i)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin n, (1 : ℝ) :=
        Finset.sum_le_sum fun i _ => Real.abs_cos_le_one (θ i)
    _ = (n : ℝ) := by simp

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

