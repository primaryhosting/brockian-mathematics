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

theorem cos_kernel_sum_sq_eq {n : ℕ} (x : Fin n → ℝ) :
    ∑ i, ∑ j, Real.cos (x i - x j) ^ 2
      = ((n : ℝ) ^ 2
          + ((∑ i, Real.cos (2 * x i)) ^ 2 + (∑ i, Real.sin (2 * x i)) ^ 2)) / 2 := by
  have inner : ∀ i : Fin n, ∑ j, Real.cos (x i - x j) ^ 2
      = ((n : ℝ) + (Real.cos (2 * x i) * (∑ j, Real.cos (2 * x j))
          + Real.sin (2 * x i) * (∑ j, Real.sin (2 * x j)))) / 2 := by
    intro i
    rw [Finset.sum_congr rfl (fun j _ => cos_sub_sq (x i) (x j)), ← Finset.sum_div]
    congr 1
    simp [Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [Finset.sum_congr rfl (fun i _ => inner i), ← Finset.sum_div]
  congr 1
  simp [Finset.sum_add_distrib, ← Finset.sum_mul, sq]

/--
**Cos Trace Norm 4001.**

For any real phases `x : Fin n → ℝ`, the cosine kernel matrix `M i j = cos (x i - x j)`
satisfies the trace/Hilbert–Schmidt bound
`(tr M)² ≤ 2 · ‖M‖_F²`,
i.e. `(tr M)² ≤ 2 · ∑ i j, (M i j)²`.

This is the sharp rank-`2` form of the Cauchy–Schwarz bound `(tr M)² ≤ rank(M) · ‖M‖_F²`:
`M = c cᵀ + s sᵀ` with `c i = cos (x i)`, `s i = sin (x i)`, so `M` is positive semidefinite
of rank at most `2`.  Equality holds exactly when the doubled phases `2 x i` sum to zero as
unit vectors (e.g. for `n = 2` with `x 0 - x 1 = π/2`).
-/
