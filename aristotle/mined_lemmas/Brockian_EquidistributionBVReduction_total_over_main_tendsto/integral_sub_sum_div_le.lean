import Mathlib

/-!
# Total Over Main Tendsto
Category: Brockian (Literature Discharge)
Target: Brockian.EquidistributionBVReduction.total_over_main_tendsto
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

set_option grind.warning false

namespace Brockian
namespace EquidistributionBVReduction

open Filter Finset

/-- The `N`-th equidistributed sample sum of `f`: the total of the values of `f` at the
`N` equidistributed sample points `0/N, 1/N, …, (N-1)/N` of the unit interval. -/

lemma integral_sub_sum_div_le (hp : MonotoneOn p (Set.Icc (0:ℝ) 1)) {N : ℕ} (hN : 0 < N) :
    (∫ x in (0:ℝ)..1, p x) - total p N / N ≤ (p 1 - p 0) / N := by
  have hN' : (N : ℝ) ≠ 0 := by
    have : (0:ℝ) < N := by exact_mod_cast hN
    positivity
  have hupper : (∫ x in (0:ℝ)..1, p x)
      ≤ ∑ k ∈ Finset.range N, p (((k : ℝ) + 1) / N) / N := by
    rw [← sum_piece_integrals hp hN]
    exact Finset.sum_le_sum fun k hk => piece_upper hp (Finset.mem_range.1 hk)
  have htel : ∑ k ∈ Finset.range N,
      (p (((k : ℝ) + 1) / N) / N - p ((k : ℝ) / N) / N) = (p 1 - p 0) / N := by
    have := Finset.sum_range_sub (f := fun k : ℕ => p ((k : ℝ) / N) / N) N
    simp only [Nat.cast_add, Nat.cast_one] at this
    rw [this, div_self hN']
    simp [sub_div]
  have hsum : total p N / N = ∑ k ∈ Finset.range N, p ((k : ℝ) / N) / N := by
    rw [total, Finset.sum_div]
  rw [hsum, ← htel, Finset.sum_sub_distrib]
  linarith [hupper]

/-- Left Riemann sums of a monotone function converge to the integral. -/
