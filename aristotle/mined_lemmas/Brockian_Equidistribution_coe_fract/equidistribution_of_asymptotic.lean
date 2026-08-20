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
Weyl's criterion for equidistribution modulo one, and its application to the
sequence `n ↦ n • α` for irrational `α`.
-/
import Mathlib

open Filter MeasureTheory Metric Set Submodule
open scoped Topology Real

namespace Brockian.Equidistribution

noncomputable section

/-! ## Definitions -/

/-- A sequence `u : ℕ → ℝ` is *equidistributed modulo one* if for every subinterval
`[a, b) ⊆ [0, 1]` the proportion of the first `N` terms whose fractional part lies in `[a, b)`
tends to `b - a`. -/

theorem equidistribution_of_asymptotic (u : ℕ → ℝ)
    (hweyl : ∀ h : ℤ, h ≠ 0 → Tendsto (weylSum u h) atTop (𝓝 0)) :
    IsEquidistributedMod1 u := by
  intro a b ha hab hb
  -- the counting function is the Cesàro average of the indicator of the arc `[a, b)`
  have hcount : ∀ N : ℕ,
      avgReal u ((arc a b).indicator 1) N
        = (((Finset.range N).filter fun k => Int.fract (u k) ∈ Ico a b).card : ℝ) / N := by
    intro N
    rw [avgReal, div_eq_inv_mul, Finset.card_filter]
    congr 1
    push_cast
    refine Finset.sum_congr rfl fun k _ => ?_
    by_cases hk : Int.fract (u k) ∈ Ico a b
    · rw [if_pos hk, Set.indicator_of_mem ((mem_arc_iff ha hb (u k)).2 hk)]
      rfl
    · rw [if_neg hk, Set.indicator_of_notMem (fun hmem => hk ((mem_arc_iff ha hb (u k)).1 hmem))]
  refine Tendsto.congr hcount ?_
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hδ : (0 : ℝ) < ε / 8 := by positivity
  -- continuous upper and lower approximations of the indicator of the arc
  have hgp_ge : ∀ z, (arc a b).indicator 1 z ≤
      rampAt (((a + b) / 2 : ℝ) : UnitAddCircle) ((b - a) / 2 + ε / 8) (ε / 8) z := by
    intro z
    by_cases hz : z ∈ arc a b
    · rw [Set.indicator_of_mem hz]
      have hd : dist z (((a + b) / 2 : ℝ) : UnitAddCircle) ≤ (b - a) / 2 :=
        arc_subset_closedBall a b hz
      rw [rampAt_eq_one hδ (by linarith)]
      simp
    · rw [Set.indicator_of_notMem hz]
      exact rampAt_nonneg _ _ _ _
  have hgp_le : ∀ z, rampAt (((a + b) / 2 : ℝ) : UnitAddCircle) ((b - a) / 2 + ε / 8) (ε / 8) z ≤
      (closedBall (((a + b) / 2 : ℝ) : UnitAddCircle) ((b - a) / 2 + ε / 8)).indicator 1 z := by
    intro z
    by_cases hz : z ∈ closedBall (((a + b) / 2 : ℝ) : UnitAddCircle) ((b - a) / 2 + ε / 8)
    · rw [Set.indicator_of_mem hz]; exact rampAt_le_one _ _ _ _
    · rw [Set.indicator_of_notMem hz]
      rw [mem_closedBall, not_le] at hz
      rw [rampAt_eq_zero hδ hz.le]
  have hgm_le : ∀ z, rampAt (((a + b) / 2 : ℝ) : UnitAddCircle) ((b - a) / 2) (ε / 8) z ≤
      (arc a b).indicator 1 z := by
    intro z
    by_cases hz : z ∈ arc a b
    · rw [Set.indicator_of_mem hz]; exact rampAt_le_one _ _ _ _
    · rw [Set.indicator_of_notMem hz]
      have hd : (b - a) / 2 ≤ dist z (((a + b) / 2 : ℝ) : UnitAddCircle) := by
        by_contra hcon
        exact hz (ball_subset_arc a b (mem_ball.2 (lt_of_not_ge hcon)))
      rw [rampAt_eq_zero hδ hd]
  have hgm_ge : ∀ z, (closedBall (((a + b) / 2 : ℝ) : UnitAddCircle)
        ((b - a) / 2 - ε / 8)).indicator 1 z ≤
      rampAt (((a + b) / 2 : ℝ) : UnitAddCircle) ((b - a) / 2) (ε / 8) z := by
    intro z
    by_cases hz : z ∈ closedBall (((a + b) / 2 : ℝ) : UnitAddCircle) ((b - a) / 2 - ε / 8)
    · rw [Set.indicator_of_mem hz, rampAt_eq_one hδ (mem_closedBall.1 hz)]
      simp
    · rw [Set.indicator_of_notMem hz]; exact rampAt_nonneg _ _ _ _
  -- bounds for the integrals of the approximations
  have hIp : ∫ z : UnitAddCircle,
      rampAt (((a + b) / 2 : ℝ) : UnitAddCircle) ((b - a) / 2 + ε / 8) (ε / 8) z
        ≤ (b - a) + 2 * (ε / 8) := by
    refine le_trans (integral_le_measureReal measurableSet_closedBall _ hgp_le) ?_
    rw [measureReal_closedBall, max_le_iff]
    refine ⟨le_trans (min_le_right _ _) (by linarith), by linarith⟩
  have hIm : (b - a) - 2 * (ε / 8) ≤ ∫ z : UnitAddCircle,
      rampAt (((a + b) / 2 : ℝ) : UnitAddCircle) ((b - a) / 2) (ε / 8) z := by
    refine le_trans ?_ (measureReal_le_integral measurableSet_closedBall _ hgm_ge)
    rw [measureReal_closedBall, min_eq_right (by linarith)]
    exact le_max_of_le_left (by linarith)
  obtain ⟨N₁, hN₁⟩ := Metric.tendsto_atTop.1 (avgReal_continuous u hweyl
    (rampAt (((a + b) / 2 : ℝ) : UnitAddCircle) ((b - a) / 2 + ε / 8) (ε / 8))) (ε / 8) hδ
  obtain ⟨N₂, hN₂⟩ := Metric.tendsto_atTop.1 (avgReal_continuous u hweyl
    (rampAt (((a + b) / 2 : ℝ) : UnitAddCircle) ((b - a) / 2) (ε / 8))) (ε / 8) hδ
  refine ⟨max N₁ N₂, fun N hN => ?_⟩
  have hup : avgReal u ((arc a b).indicator 1) N ≤ avgReal u
      (rampAt (((a + b) / 2 : ℝ) : UnitAddCircle) ((b - a) / 2 + ε / 8) (ε / 8)) N := by
    refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun k _ => hgp_ge _) (by positivity)
  have hdn : avgReal u (rampAt (((a + b) / 2 : ℝ) : UnitAddCircle) ((b - a) / 2) (ε / 8)) N
      ≤ avgReal u ((arc a b).indicator 1) N := by
    refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun k _ => hgm_le _) (by positivity)
  have h1 := hN₁ N (le_trans (le_max_left _ _) hN)
  have h2 := hN₂ N (le_trans (le_max_right _ _) hN)
  rw [Real.dist_eq, abs_lt] at h1 h2 ⊢
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

/-! ## Discharging the hypothesis for `n • α` with `α` irrational -/

