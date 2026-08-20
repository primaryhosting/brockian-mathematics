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

import Mathlib

/-!
# Equidistribution of `n • α` and the reduction of configuration counts to the main term

For an irrational `α`, the configuration count

`configCount α a b N = #{ n < N : Int.fract (n * α) ∈ [a, b) }`

is asymptotic to its main term `mainTerm a b N = (b - a) * N`.

The analytic input (Weyl equidistribution of the sequence `n • α` on the circle `ℝ / ℤ`)
is proved here from scratch, so the final statement
`configCount_over_main_tendsto` is unconditional.

The proof proceeds by:
* computing the Birkhoff averages of the Fourier monomials `fourier k` along the orbit
  (geometric sums, `avg_fourier_tendsto`);
* extending to all continuous functions by Stone--Weierstrass (`avg_continuous_tendsto`);
* sandwiching the indicator of an arc between continuous piecewise-linear functions
  (a bounded-variation reduction) to obtain the counting asymptotics.
-/

open Filter MeasureTheory Set Topology Complex
open scoped BigOperators

set_option autoImplicit false

namespace Brockian

namespace EquidistributionBVReduction

noncomputable section

local instance isProbabilityMeasure_volume_unitAddCircle :
    IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  ⟨UnitAddCircle.measure_univ⟩

/-- The point `n * α` of the circle `ℝ / ℤ`. -/

theorem configCount_div_tendsto {alpha : ℝ} (halpha : Irrational alpha) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1) :
    Tendsto (fun N : ℕ => (configCount alpha a b N : ℝ) / N) atTop (𝓝 (b - a)) := by
  by_cases hfull : b - a = 1
  · have ha0 : a = 0 := by linarith
    have hb1 : b = 1 := by linarith
    subst ha0
    subst hb1
    have hcount : ∀ N : ℕ, configCount alpha 0 1 N = N := by
      intro N
      rw [configCount, Finset.filter_true_of_mem (fun n _ => ⟨Int.fract_nonneg _,
        Int.fract_lt_one _⟩), Finset.card_range]
    refine Tendsto.congr' ?_ (tendsto_const_nhds (x := (1 : ℝ) - 0))
    filter_upwards [eventually_ne_atTop 0] with N hN
    rw [hcount N]
    field_simp
    norm_num
  · have hlt : b - a < 1 := lt_of_le_of_ne (by linarith) hfull
    rw [Metric.tendsto_atTop]
    intro ε hε
    set eps : ℝ := min (ε / 4) (min ((b - a) / 2) ((1 - (b - a)) / 3)) with hepsdef
    have heps : 0 < eps :=
      lt_min (by linarith) (lt_min (by linarith) (by linarith))
    have he1 : eps ≤ ε / 4 := min_le_left _ _
    have he2 : eps ≤ (b - a) / 2 := le_trans (min_le_right _ _) (min_le_left _ _)
    have he3 : eps ≤ (1 - (b - a)) / 3 := le_trans (min_le_right _ _) (min_le_right _ _)
    obtain ⟨hup, hup_pt, hup_int⟩ := exists_upper_sandwich (a := a) (b := b) hab.le heps
      (by linarith)
    obtain ⟨glo, glo_pt, glo_int⟩ := exists_lower_sandwich (a := a) (b := b) ha hb heps
      (by linarith) (by linarith)
    obtain ⟨N1, hN1⟩ :=
      (Metric.tendsto_atTop.mp (avg_continuous_tendsto_real halpha hup)) eps heps
    obtain ⟨N2, hN2⟩ :=
      (Metric.tendsto_atTop.mp (avg_continuous_tendsto_real halpha glo)) eps heps
    refine ⟨max 1 (max N1 N2), fun N hN => ?_⟩
    have hN0 : 1 ≤ N := le_trans (le_max_left _ _) hN
    have hN1' : N1 ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_right 1 _)) hN
    have hN2' : N2 ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_right 1 _)) hN
    have hNpos : (0 : ℝ) < N := by exact_mod_cast hN0
    have hle_up : (configCount alpha a b N : ℝ) / N ≤ avg alpha hup N := by
      rw [configCount_eq_sum, avg, smul_eq_mul, div_eq_inv_mul]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      refine Finset.sum_le_sum fun n _ => ?_
      exact hup_pt ((n : ℝ) * alpha)
    have hge_lo : avg alpha glo N ≤ (configCount alpha a b N : ℝ) / N := by
      rw [configCount_eq_sum, avg, smul_eq_mul, div_eq_inv_mul]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      refine Finset.sum_le_sum fun n _ => ?_
      exact glo_pt ((n : ℝ) * alpha)
    have hu : avg alpha hup N < (∫ x : UnitAddCircle, hup x) + eps := by
      have h := hN1 N hN1'
      rw [Real.dist_eq, abs_lt] at h
      linarith [h.2]
    have hl : (∫ x : UnitAddCircle, glo x) - eps < avg alpha glo N := by
      have h := hN2 N hN2'
      rw [Real.dist_eq, abs_lt] at h
      linarith [h.1]
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith

/-- The configuration count is asymptotic to its main term. -/
