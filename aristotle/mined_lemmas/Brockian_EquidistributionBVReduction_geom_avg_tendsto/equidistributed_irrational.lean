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
# Equidistribution of irrational rotations and the bounded-variation reduction

This file develops, from scratch, Weyl's equidistribution theorem for the sequence
`n ↦ n • α mod 1` (`α` irrational) and reduces averages of functions of bounded variation
to their integral.

The final result `total_over_main_tendsto` states that, for a function `f` of bounded
variation on `[0,1]` with nonzero integral, the *total*
`∑_{n < N} f (fract (n α))` divided by the *main term* `N * ∫₀¹ f` tends to `1`.
-/

open Filter Finset Set MeasureTheory Metric
open scoped Topology

namespace Brockian.EquidistributionBVReduction

noncomputable section

/-- A sequence of reals is equidistributed mod one when, for every subinterval `[a,b) ⊆ [0,1]`,
the proportion of the first `N` fractional parts lying in `[a, b)` tends to `b - a`. -/

theorem equidistributed_irrational {α : ℝ} (hα : Irrational α) :
    EquidistributedMod1 (fun n : ℕ => n * α) := by
  intro a b ha hab hb
  refine tendsto_of_eventually_abs_sub_le (fun ε hε => ?_)
  set δ : ℝ := ε/4 with hδdef
  have hδ : 0 < δ := by positivity
  set c : AddCircle (1:ℝ) := (((a+b)/2 : ℝ) : AddCircle (1:ℝ)) with hc
  set r : ℝ := (b-a)/2 with hr
  have hr0 : 0 ≤ r := by linarith [hr]
  have hr1 : 2 * r ≤ 1 := by linarith [hr]
  have hcoe : ∀ n : ℕ, (((n:ℝ) * α : ℝ) : AddCircle (1:ℝ))
      = ((Int.fract ((n:ℝ)*α) : ℝ) : AddCircle (1:ℝ)) := fun n => (AddCircle.coe_fract _).symm
  have hterm_up : ∀ n : ℕ, (if Int.fract ((n:ℝ)*α) ∈ Ico a b then (1:ℝ) else 0)
      ≤ bump c r δ ((((n:ℝ) * α : ℝ)) : AddCircle (1:ℝ)) := by
    intro n
    by_cases hmem : Int.fract ((n:ℝ)*α) ∈ Ico a b
    · rw [if_pos hmem]
      refine le_of_eq (bump_eq_one hδ ?_).symm
      rw [hcoe n, hc]
      refine le_trans (dist_coe_le _ _) ?_
      rw [abs_le]
      obtain ⟨h1, h2⟩ := hmem
      constructor <;> linarith [hr]
    · rw [if_neg hmem]; exact bump_nonneg _ _ _ _
  have hterm_lo : ∀ n : ℕ, bump c (r-δ) δ ((((n:ℝ) * α : ℝ)) : AddCircle (1:ℝ))
      ≤ (if Int.fract ((n:ℝ)*α) ∈ Ico a b then (1:ℝ) else 0) := by
    intro n
    by_cases hmem : Int.fract ((n:ℝ)*α) ∈ Ico a b
    · rw [if_pos hmem]; exact bump_le_one _ _ _ _
    · rw [if_neg hmem]
      by_contra hcon
      push_neg at hcon
      have hd := dist_lt_of_bump_pos hδ hcon
      rw [hcoe n, hc] at hd
      have hd' : dist ((Int.fract ((n:ℝ)*α) : ℝ) : AddCircle (1:ℝ))
          (((a+b)/2 : ℝ) : AddCircle (1:ℝ)) < (b-a)/2 := by simpa [hr] using hd
      exact hmem (mem_Ico_of_dist_lt ha hab hb (Int.fract_nonneg _) (Int.fract_lt_one _) hd')
  have hcard : ∀ N : ℕ,
      (((range N).filter fun n : ℕ => Int.fract ((n:ℝ)*α) ∈ Ico a b).card : ℝ)
        = ∑ n ∈ range N, (if Int.fract ((n:ℝ)*α) ∈ Ico a b then (1:ℝ) else 0) := by
    intro N
    rw [card_filter]
    push_cast
    rfl
  -- the two comparison sequences
  set U : ℕ → ℝ :=
    fun N => (∑ n ∈ range N, bump c r δ ((((n:ℝ) * α : ℝ)) : AddCircle (1:ℝ)))/(N:ℝ) with hU
  set L : ℕ → ℝ :=
    fun N => (∑ n ∈ range N, bump c (r-δ) δ ((((n:ℝ) * α : ℝ)) : AddCircle (1:ℝ)))/(N:ℝ) with hL
  have hUlim : Tendsto U atTop (𝓝 (∫ t : AddCircle (1:ℝ), bump c r δ t)) :=
    avg_tendsto_continuous_real hα _ (continuous_bump c r δ)
  have hLlim : Tendsto L atTop (𝓝 (∫ t : AddCircle (1:ℝ), bump c (r-δ) δ t)) :=
    avg_tendsto_continuous_real hα _ (continuous_bump c (r-δ) δ)
  have hUint : (∫ t : AddCircle (1:ℝ), bump c r δ t) ≤ (b - a) + 2*δ := by
    refine le_trans (integral_bump_le hδ (by linarith)) ?_
    refine le_trans (min_le_right _ _) ?_
    linarith [hr]
  have hLint : (b - a) - 2*δ ≤ ∫ t : AddCircle (1:ℝ), bump c (r-δ) δ t := by
    rcases le_or_gt δ r with hcase | hcase
    · refine le_trans ?_ (le_integral_bump hδ (by linarith))
      rw [le_min_iff]
      constructor
      · linarith [hr]
      · linarith [hr]
    · have hnonneg : 0 ≤ ∫ t : AddCircle (1:ℝ), bump c (r-δ) δ t :=
        integral_nonneg (fun t => bump_nonneg _ _ _ _)
      refine le_trans ?_ hnonneg
      linarith [hr]
  obtain ⟨N₁, hN₁⟩ := Metric.tendsto_atTop.1 hUlim δ hδ
  obtain ⟨N₂, hN₂⟩ := Metric.tendsto_atTop.1 hLlim δ hδ
  filter_upwards [eventually_ge_atTop (max N₁ N₂)] with N hN
  have hN1 : N₁ ≤ N := le_trans (le_max_left _ _) hN
  have hN2 : N₂ ≤ N := le_trans (le_max_right _ _) hN
  have hUN := hN₁ N hN1
  have hLN := hN₂ N hN2
  rw [Real.dist_eq, abs_lt] at hUN hLN
  have hNnn : (0:ℝ) ≤ (N:ℝ) := Nat.cast_nonneg N
  have hup : (((range N).filter fun n : ℕ => Int.fract ((n:ℝ)*α) ∈ Ico a b).card : ℝ)/(N:ℝ)
      ≤ U N := by
    rw [hcard N, hU]
    exact div_le_div_of_nonneg_right (sum_le_sum fun n _ => hterm_up n) hNnn
  have hlo : L N ≤ (((range N).filter fun n : ℕ => Int.fract ((n:ℝ)*α) ∈ Ico a b).card : ℝ)/(N:ℝ) := by
    rw [hcard N, hL]
    exact div_le_div_of_nonneg_right (sum_le_sum fun n _ => hterm_lo n) hNnn
  rw [abs_le]
  constructor
  · have : (b - a) - 3*δ ≤ L N := by linarith [hLN.1, hLint]
    have hδε : 3*δ ≤ ε := by rw [hδdef]; linarith
    linarith
  · have : U N ≤ (b - a) + 3*δ := by linarith [hUN.2, hUint]
    have hδε : 3*δ ≤ ε := by rw [hδdef]; linarith
    linarith

/-! ### Step 4: from intervals to monotone functions -/

/-- Membership in a grid interval is detected by the floor function. -/
