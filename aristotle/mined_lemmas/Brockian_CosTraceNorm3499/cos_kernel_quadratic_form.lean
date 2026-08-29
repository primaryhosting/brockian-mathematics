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

open Finset Real

/-- The quadratic form of the "cosine kernel" matrix `C i j = cos (θ i - θ j)` is the
sum of two squares. -/

theorem cos_kernel_quadratic_form (n : ℕ) (θ v : Fin n → ℝ) :
    ∑ i, ∑ j, Real.cos (θ i - θ j) * (v i * v j)
      = (∑ i, v i * Real.cos (θ i)) ^ 2 + (∑ i, v i * Real.sin (θ i)) ^ 2 := by
  have hpt : ∀ i j : Fin n, Real.cos (θ i - θ j) * (v i * v j)
      = (v i * Real.cos (θ i)) * (v j * Real.cos (θ j))
        + (v i * Real.sin (θ i)) * (v j * Real.sin (θ j)) := by
    intro i j
    rw [Real.cos_sub]; ring
  rw [sq, sq, Finset.sum_mul_sum, Finset.sum_mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun j _ => hpt i j

/-- **Cos Trace Norm 3499.**
For any phases `θ : Fin n → ℝ` and any real vector `v`, the quadratic form of the
cosine kernel matrix `C i j = cos (θ i - θ j)` is bounded in absolute value by
`n * ‖v‖²`; here `n = trace C` is the trace norm of the (positive semidefinite,
rank ≤ 2) matrix `C`. -/
