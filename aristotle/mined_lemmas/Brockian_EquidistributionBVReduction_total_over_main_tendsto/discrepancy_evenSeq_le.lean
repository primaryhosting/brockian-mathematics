import Brockian.EquidistributionBVReduction

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

/-
# Total Over Main Tendsto
Category: Brockian (Literature Discharge)
Target: Brockian.EquidistributionBVReduction.total_over_main_tendsto
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Total Over Main Tendsto
Category: Brockian (Literature Discharge)
Target: Brockian.EquidistributionBVReduction.total_over_main_tendsto
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open Filter Topology

namespace Brockian
namespace EquidistributionBVReduction

/-- The number of indices `n < N` for which the sequence value `x n` lies in `[0, a)`,
viewed as a real number.  This is the *total* count appearing in the bounded–variation
reduction step of an equidistribution argument. -/

theorem discrepancy_evenSeq_le (N : ℕ) (hN : 0 < N) :
    discrepancy evenSeq (1 / 2) N ≤ 1 / (N : ℝ) := by
  rw [discrepancy, count_evenSeq]
  have h1 : 2 * ((N + 1) / 2) + (N + 1) % 2 = N + 1 := Nat.div_add_mod (N + 1) 2
  have h2 : (N + 1) % 2 < 2 := Nat.mod_lt _ (by norm_num)
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  set c : ℝ := (((N + 1) / 2 : ℕ) : ℝ) with hc
  have h1' : 2 * c + (((N + 1) % 2 : ℕ) : ℝ) = (N : ℝ) + 1 := by
    have := congrArg (fun k : ℕ => (k : ℝ)) h1
    push_cast at this
    linarith [this]
  have h2' : (((N + 1) % 2 : ℕ) : ℝ) < 2 := by exact_mod_cast h2
  have h3 : (0 : ℝ) ≤ (((N + 1) % 2 : ℕ) : ℝ) := Nat.cast_nonneg _
  have key : c / (N : ℝ) - 1 / 2 = (2 * c - (N : ℝ)) / (2 * (N : ℝ)) := by field_simp
  rw [key, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 * (N : ℝ))]
  have habs : |2 * c - (N : ℝ)| ≤ 1 := by
    rw [abs_le]; constructor <;> linarith
  calc |2 * c - (N : ℝ)| / (2 * (N : ℝ)) ≤ 1 / (2 * (N : ℝ)) := by gcongr
    _ ≤ 1 / (N : ℝ) := by
        apply div_le_div_of_nonneg_left (by norm_num) hNR
        linarith

/-- An instance of `total_over_main_tendsto` with density `a = 1/2`: for the two-periodic
sequence `evenSeq`, the total count over the main term `N / 2` tends to `1`. -/
