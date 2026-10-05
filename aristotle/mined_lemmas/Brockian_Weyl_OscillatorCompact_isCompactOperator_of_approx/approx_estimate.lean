/-
  CompactCriterion.lean — an abstract compactness criterion: an operator whose
  unit-ball image is uniformly approximable by finite-dimensional subspaces is
  a compact operator.
-/
import Mathlib

open Metric Filter

namespace Brockian.Weyl.OscillatorCompact

/-- An operator whose closed-unit-ball image is uniformly approximable by
finite-dimensional subspaces is a compact operator. -/

theorem approx_estimate (g : SchwartzMap ℝ ℂ) {Rr hh : ℝ} (hRr : 0 < Rr) (hh0 : 0 < hh)
    {n : ℕ} (hn : -Rr + n * hh = Rr) :
    ‖schwartzToL2 g - stepLp (fun j => g (-Rr + (j + 1) * hh)) Rr hh n‖ ^ 2
      ≤ hh ^ 2 * (∫ x : ℝ, ‖deriv (g : ℝ → ℂ) x‖ ^ 2)
        + (∫ x : ℝ, x ^ 2 * ‖g x‖ ^ 2) / Rr ^ 2 := by
  classical
  set c : ℕ → ℂ := fun j => g (-Rr + (j + 1) * hh) with hc
  set v : L2R := stepLp c Rr hh n with hv
  set u : L2R := schwartzToL2 g with hu
  set F : ℝ → ℝ := fun x => ‖g x - stepVal c Rr hh n x‖ ^ 2 with hF
  have hdint := integrable_deriv_sq g
  have hqint := integrable_weight_sq g
  -- identification of `u - v` with `g - s`
  have hae : ⇑(u - v) =ᵐ[volume] fun x => g x - stepVal c Rr hh n x := by
    filter_upwards [Lp.coeFn_sub u v, SchwartzMap.coeFn_toLp g 2 (volume : Measure ℝ),
      stepLp_coeFn c Rr hh n] with x h1 h2 h3
    rw [h1]
    simp only [Pi.sub_apply]
    rw [hu, schwartzToL2_apply, h2, hv, h3]
  have hnormsq : ‖u - v‖ ^ 2 = ∫ x : ℝ, F x := by
    rw [norm_sq_eq_integral]
    exact integral_congr_ae (by filter_upwards [hae] with x hx; rw [hx])
  have hFint : Integrable F volume := by
    have h2 := (memLp_two_iff_integrable_sq_norm
      (Lp.aestronglyMeasurable (u - v))).mp (Lp.memLp (u - v))
    exact h2.congr (by filter_upwards [hae] with x hx; rw [hx])
  -- split the integral over `(-R, R]` and its complement
  set U : Set ℝ := Set.Ioc (-Rr) Rr with hU
  have hUeq : (⋃ j ∈ Finset.range n, cellSet Rr hh j) = U := by
    rw [cells_union Rr hh hh0.le n, hn]
  have hsplit : (∫ x in U, F x) + (∫ x in Uᶜ, F x) = ∫ x : ℝ, F x :=
    integral_add_compl measurableSet_Ioc hFint
  -- inside: sum over the cells
  have hUsum : ∫ x in U, F x = ∑ j ∈ Finset.range n, ∫ x in cellSet Rr hh j, F x := by
    rw [← hUeq]
    exact integral_biUnion_finset _ (fun _ _ => measurableSet_Ioc)
      ((cells_disjoint Rr hh hh0).set_pairwise _) (fun _ _ => hFint.integrableOn)
  have hcellbd : ∀ j ∈ Finset.range n, ∫ x in cellSet Rr hh j, F x
      ≤ hh ^ 2 * ∫ x in cellSet Rr hh j, ‖deriv (g : ℝ → ℂ) x‖ ^ 2 := by
    intro j hj
    have hjn := Finset.mem_range.mp hj
    have heq : ∫ x in cellSet Rr hh j, F x
        = ∫ x in Set.Ioc (-Rr + j * hh) (-Rr + ((j : ℝ) + 1) * hh),
            ‖g x - g (-Rr + ((j : ℝ) + 1) * hh)‖ ^ 2 := by
      refine setIntegral_congr_fun measurableSet_Ioc fun x hx => ?_
      have : stepVal c Rr hh n x = c j := stepVal_of_mem c hh0 hjn hx
      rw [hF]
      simp only
      rw [this, hc]
    rw [heq]
    have hcell := cell_estimate g (a := -Rr + (j : ℝ) * hh) (b := -Rr + ((j : ℝ) + 1) * hh)
      (by nlinarith)
    have hba : (-Rr + ((j : ℝ) + 1) * hh) - (-Rr + (j : ℝ) * hh) = hh := by ring
    rw [hba] at hcell
    exact hcell
  have hsum2 : ∑ j ∈ Finset.range n, hh ^ 2 * ∫ x in cellSet Rr hh j,
      ‖deriv (g : ℝ → ℂ) x‖ ^ 2
      = hh ^ 2 * ∫ x in U, ‖deriv (g : ℝ → ℂ) x‖ ^ 2 := by
    rw [← Finset.mul_sum, ← integral_biUnion_finset (s := cellSet Rr hh) _
      (fun _ _ => measurableSet_Ioc)
      ((cells_disjoint Rr hh hh0).set_pairwise _) (fun _ _ => hdint.integrableOn), hUeq]
  have hinside : ∫ x in U, F x ≤ hh ^ 2 * ∫ x : ℝ, ‖deriv (g : ℝ → ℂ) x‖ ^ 2 := by
    have h1 : ∫ x in U, F x
        ≤ ∑ j ∈ Finset.range n, hh ^ 2 * ∫ x in cellSet Rr hh j,
            ‖deriv (g : ℝ → ℂ) x‖ ^ 2 := by
      rw [hUsum]; exact Finset.sum_le_sum hcellbd
    rw [hsum2] at h1
    have h2 : ∫ x in U, ‖deriv (g : ℝ → ℂ) x‖ ^ 2 ≤ ∫ x : ℝ, ‖deriv (g : ℝ → ℂ) x‖ ^ 2 :=
      setIntegral_le_integral hdint (Filter.Eventually.of_forall fun _ => by positivity)
    nlinarith [sq_nonneg hh, h1, h2]
  -- outside: the confining weight
  have htail : ∫ x in Uᶜ, F x ≤ (∫ x : ℝ, x ^ 2 * ‖g x‖ ^ 2) / Rr ^ 2 := by
    have hFeq : ∀ x ∈ Uᶜ, F x ≤ x ^ 2 * ‖g x‖ ^ 2 / Rr ^ 2 := by
      intro x hx
      have hstep : stepVal c Rr hh n x = 0 := by
        refine stepVal_of_notMem c hh0.le ?_
        rw [hn]; exact hx
      have hFx : F x = ‖g x‖ ^ 2 := by rw [hF]; simp only; rw [hstep, sub_zero]
      have hx2 : Rr ^ 2 ≤ x ^ 2 := by
        rw [hU, Set.mem_compl_iff, Set.mem_Ioc, not_and_or, not_lt, not_le] at hx
        rcases hx with h | h
        · nlinarith
        · nlinarith
      rw [hFx, le_div_iff₀ (by positivity)]
      nlinarith [sq_nonneg ‖g x‖, norm_nonneg (g x)]
    have hmono : ∫ x in Uᶜ, F x ≤ ∫ x in Uᶜ, x ^ 2 * ‖g x‖ ^ 2 / Rr ^ 2 :=
      setIntegral_mono_on hFint.integrableOn
        ((hqint.div_const (Rr ^ 2)).integrableOn) measurableSet_Ioc.compl hFeq
    have hdiv : ∫ x in Uᶜ, x ^ 2 * ‖g x‖ ^ 2 / Rr ^ 2
        = (∫ x in Uᶜ, x ^ 2 * ‖g x‖ ^ 2) / Rr ^ 2 := by
      rw [integral_div]
    have hle : ∫ x in Uᶜ, x ^ 2 * ‖g x‖ ^ 2 ≤ ∫ x : ℝ, x ^ 2 * ‖g x‖ ^ 2 :=
      setIntegral_le_integral hqint (Filter.Eventually.of_forall fun _ => by positivity)
    rw [hdiv] at hmono
    have hpos : (0:ℝ) < Rr ^ 2 := by positivity
    calc ∫ x in Uᶜ, F x ≤ (∫ x in Uᶜ, x ^ 2 * ‖g x‖ ^ 2) / Rr ^ 2 := hmono
      _ ≤ (∫ x : ℝ, x ^ 2 * ‖g x‖ ^ 2) / Rr ^ 2 := by
          exact div_le_div_of_nonneg_right hle hpos.le
  rw [hnormsq, ← hsplit]
  linarith [hinside, htail]

end Brockian.Weyl.Rellich

/-! ### The energy form and the good set -/

namespace Brockian.Weyl.OscillatorCompact

open Brockian.Weyl.SchrodingerMinimal
open Brockian.Weyl.HarmonicOscillator
open Brockian.Weyl.Rellich

/-- The oscillator energy of a Schwartz function. -/
