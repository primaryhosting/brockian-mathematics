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

import Mathlib

/-!
# Goldbach Covariance Transfer
Category: Brockian Conjecture
Target: Brockian.GoldbachComb.GoldbachCovarianceTransfer
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(Note: Lean 4 requires `import` lines to precede every other command, including module
docstrings, so the requested header comment appears immediately after the import.)
-/

open scoped BigOperators

namespace Brockian.GoldbachComb

/-- The Goldbach representation count of `n`: the number of ordered pairs `(a, n - a)`
with `a ≤ n` such that both `a` and `n - a` are prime. -/

theorem sum_convolution_eq_bilinear (f : ℕ → ℝ) (N : ℕ) :
    ∑ n ∈ Finset.range (N + 1), ∑ a ∈ Finset.range (n + 1), f a * f (n - a)
      = ∑ p ∈ Finset.range (N + 1), ∑ q ∈ Finset.range (N + 1),
          (if p + q ≤ N then f p * f q else 0) := by
  classical
  -- rewrite the right-hand side as a sum over the triangle
  have hR : ∑ p ∈ Finset.range (N + 1), ∑ q ∈ Finset.range (N + 1),
        (if p + q ≤ N then f p * f q else 0)
      = ∑ pq ∈ ((Finset.range (N + 1)) ×ˢ (Finset.range (N + 1))).filter
          (fun pq : ℕ × ℕ => pq.1 + pq.2 ≤ N), f pq.1 * f pq.2 := by
    rw [Finset.sum_filter, Finset.sum_product]
  rw [hR]
  -- partition the triangle according to the value of `p + q`
  have hmaps : ∀ pq ∈ ((Finset.range (N + 1)) ×ˢ (Finset.range (N + 1))).filter
      (fun pq : ℕ × ℕ => pq.1 + pq.2 ≤ N), pq.1 + pq.2 ∈ Finset.range (N + 1) := by
    intro pq hpq
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hpq ⊢
    omega
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  refine Finset.sum_congr rfl ?_
  intro n hn
  simp only [Finset.mem_range] at hn
  have hfib : (((Finset.range (N + 1)) ×ˢ (Finset.range (N + 1))).filter
      (fun pq : ℕ × ℕ => pq.1 + pq.2 ≤ N)).filter (fun pq : ℕ × ℕ => pq.1 + pq.2 = n)
      = Finset.antidiagonal n := by
    ext pq
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range,
      Finset.mem_antidiagonal]
    constructor
    · rintro ⟨-, h⟩; exact h
    · intro h; omega
  rw [hfib, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]

/-- The Goldbach count is the diagonal correlation of the prime indicator. -/
