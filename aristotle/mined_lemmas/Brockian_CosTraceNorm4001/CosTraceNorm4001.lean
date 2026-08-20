import Mathlib

/-!
# Cos Trace Norm 4001
Category: Brockian Corpus
Target: Brockian.CosTraceNorm4001
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Brockian

/-- Product-to-sum expansion of `cos (a - b) ^ 2`. -/

theorem CosTraceNorm4001 {n : ℕ} (x : Fin n → ℝ) (M : Matrix (Fin n) (Fin n) ℝ)
    (hM : ∀ i j, M i j = Real.cos (x i - x j)) :
    M.trace ^ 2 ≤ 2 * ∑ i, ∑ j, M i j ^ 2 := by
  have htr : M.trace = (n : ℝ) := by
    simp [Matrix.trace, Matrix.diag, hM]
  have hsum : ∑ i, ∑ j, M i j ^ 2 = ∑ i, ∑ j, Real.cos (x i - x j) ^ 2 := by
    simp [hM]
  rw [htr, hsum, cos_kernel_sum_sq_eq]
  have h1 : (0 : ℝ) ≤ (∑ i, Real.cos (2 * x i)) ^ 2 := sq_nonneg _
  have h2 : (0 : ℝ) ≤ (∑ i, Real.sin (2 * x i)) ^ 2 := sq_nonneg _
  linarith

end Brockian


