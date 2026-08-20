import Mathlib
/-!
# Density Zero Reduction
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.density_zero_reduction
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
namespace BetrothedNumbers

open Filter Finset

/-! ## Natural density -/

/-- The number of elements of `A` in the interval `[1, N]`. -/

private lemma sum_one_div_sq_le_aux (N : ℕ) (hN : 1 ≤ N) :
    ∑ d ∈ Finset.Icc 1 N, (1 : ℝ) / (d : ℝ) ^ 2 ≤ 2 - 1 / N := by
  induction N, hN using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
      rw [Finset.sum_Icc_succ_top (by omega)]
      have hnpos : (0:ℝ) < n := by exact_mod_cast hn
      have h1 : (1:ℝ)/((n:ℝ)+1)^2 ≤ 1/n - 1/((n:ℝ)+1) := by
        rw [div_sub_div _ _ (ne_of_gt hnpos) (by positivity),
          div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith
      push_cast
      linarith

/-- `∑_{d ≤ N} 1/d² ≤ 2`. -/
