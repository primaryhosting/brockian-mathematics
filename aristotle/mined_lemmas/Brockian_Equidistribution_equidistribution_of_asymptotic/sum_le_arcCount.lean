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

lemma sum_le_arcCount (x : ℕ → ℝ) {a b ε : ℝ} (hε : 0 < ε) (ha : 0 ≤ a) (hb : b ≤ 1) (N : ℕ) :
    ∑ n ∈ Finset.range N,
        plateau (((a + b) / 2 : ℝ) : 𝕋) ((b - a) / 2 - ε) ε ((x n : ℝ) : 𝕋)
      ≤ (arcCount x a b N : ℝ) := by
  rw [arcCount_cast]
  refine Finset.sum_le_sum (fun n _ => ?_)
  by_cases hn : Int.fract (x n) ∈ Set.Ico a b
  · rw [if_pos hn]; exact plateau_le_one _ _ _ _
  · rw [if_neg hn]
    refine le_of_eq (plateau_eq_zero hε ?_)
    have : ¬ dist ((x n : ℝ) : 𝕋) (((a + b) / 2 : ℝ) : 𝕋) < (b - a) / 2 := fun hlt =>
      hn (fract_mem_of_dist_lt ha hb hlt)
    push_neg at this
    linarith

/-- **Weyl's equidistribution theorem.** If all nontrivial exponential sums of a real sequence
`x` have vanishing Cesàro averages, then the sequence is equidistributed modulo one: for every
subinterval `[a, b) ⊆ [0, 1]` the proportion of the first `N` terms whose fractional part lies
in `[a, b)` tends to `b - a`. -/
