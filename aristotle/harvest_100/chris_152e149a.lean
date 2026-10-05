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
theorem CosTraceNorm3499 (n : ℕ) (θ v : Fin n → ℝ) :
    |∑ i, ∑ j, Real.cos (θ i - θ j) * (v i * v j)| ≤ n * ∑ i, (v i) ^ 2 := by
  have hform := cos_kernel_quadratic_form n θ v
  have hnonneg : 0 ≤ ∑ i, ∑ j, Real.cos (θ i - θ j) * (v i * v j) := by
    rw [hform]; positivity
  rw [abs_of_nonneg hnonneg, hform]
  have hc := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ v (fun i => Real.cos (θ i))
  have hs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ v (fun i => Real.sin (θ i))
  have hsum : (∑ i, (v i) ^ 2) * (∑ i : Fin n, Real.cos (θ i) ^ 2)
      + (∑ i, (v i) ^ 2) * (∑ i : Fin n, Real.sin (θ i) ^ 2)
      = (n : ℝ) * ∑ i, (v i) ^ 2 := by
    rw [← mul_add, ← Finset.sum_add_distrib]
    have : ∀ i : Fin n, Real.cos (θ i) ^ 2 + Real.sin (θ i) ^ 2 = 1 := by
      intro i; exact Real.cos_sq_add_sin_sq (θ i)
    simp [this, mul_comm]
  calc (∑ i, v i * Real.cos (θ i)) ^ 2 + (∑ i, v i * Real.sin (θ i)) ^ 2
      ≤ (∑ i, (v i) ^ 2) * (∑ i : Fin n, Real.cos (θ i) ^ 2)
        + (∑ i, (v i) ^ 2) * (∑ i : Fin n, Real.sin (θ i) ^ 2) := add_le_add hc hs
    _ = (n : ℝ) * ∑ i, (v i) ^ 2 := hsum

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

