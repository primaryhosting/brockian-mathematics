import Mathlib

/-!
# Equidistribution Of Asymptotic
Category: Brockian (Open Discharge)
Target: Brockian.Equidistribution.equidistribution_of_asymptotic
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

namespace Brockian.Equidistribution

open MeasureTheory Filter Topology Metric Finset

noncomputable section

local notation "𝕋" => AddCircle (1 : ℝ)

/-! ### Cesàro averages along a sequence -/

/-- The Cesàro average of a function `f` on the circle `ℝ/ℤ` along the first `N` terms of a
real sequence `x`. -/

lemma arcCount_le_sum (x : ℕ → ℝ) {a b ε : ℝ} (hε : 0 < ε) (N : ℕ) :
    (arcCount x a b N : ℝ)
      ≤ ∑ n ∈ Finset.range N,
          plateau (((a + b) / 2 : ℝ) : 𝕋) ((b - a) / 2) ε ((x n : ℝ) : 𝕋) := by
  rw [arcCount_cast]
  refine Finset.sum_le_sum (fun n _ => ?_)
  by_cases hn : Int.fract (x n) ∈ Set.Ico a b
  · rw [if_pos hn, plateau_eq_one hε (dist_le_of_fract_mem hn)]
  · rw [if_neg hn]; exact plateau_nonneg _ _ _ _

