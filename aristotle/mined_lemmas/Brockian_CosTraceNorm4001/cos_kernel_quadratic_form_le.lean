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

theorem cos_kernel_quadratic_form_le (n : ℕ) (x v : Fin n → ℝ) :
    v ⬝ᵥ (cosKernel n x *ᵥ v) ≤ (n : ℝ) * ∑ i, (v i) ^ 2 := by
  rw [cos_kernel_dotProduct, cos_kernel_quadratic_form]
  have hc : (∑ i, v i * Real.cos (x i)) ^ 2
      ≤ (∑ i, (v i) ^ 2) * ∑ i, (Real.cos (x i)) ^ 2 :=
    Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  have hs : (∑ i, v i * Real.sin (x i)) ^ 2
      ≤ (∑ i, (v i) ^ 2) * ∑ i, (Real.sin (x i)) ^ 2 :=
    Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  have hsum : (∑ i, (Real.cos (x i)) ^ 2) + (∑ i, (Real.sin (x i)) ^ 2) = (n : ℝ) := by
    rw [← Finset.sum_add_distrib]
    simp [Real.cos_sq_add_sin_sq]
  have h := add_le_add hc hs
  rw [← mul_add, hsum, mul_comm] at h
  exact h

/-- **Cos Trace Norm 4001.**
For every family of phases `x : Fin 4001 → ℝ`, the cosine kernel matrix
`C i j = cos (x i - x j)` is positive semidefinite, its trace equals `4001` (so its trace norm,
the sum of its singular values, is `4001`), and its quadratic form obeys the corresponding
trace-norm bound `⟪v, C v⟫ ≤ 4001 * ‖v‖²`, with `0 ≤ ⟪v, C v⟫`, for every real vector `v`. -/
