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

lemma uIcc_subset_unit {N k : ℕ} (hk : k < N) :
    Set.uIcc ((k : ℝ) / N) (((k : ℝ) + 1) / N) ⊆ Set.Icc (0 : ℝ) 1 := by
  have hN : (0 : ℝ) < N := by
    have : 0 < N := lt_of_le_of_lt (Nat.zero_le k) hk
    exact_mod_cast this
  rw [Set.uIcc_of_le (by gcongr; linarith)]
  apply Set.Icc_subset_Icc
  · positivity
  · rw [div_le_one hN]
    have : (k : ℝ) + 1 ≤ N := by exact_mod_cast hk
    linarith

/-- A monotone function is interval integrable on each piece of the uniform partition. -/
