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

theorem cell_estimate (g : SchwartzMap ℝ ℂ) {a b : ℝ} (hab : a ≤ b) :
    ∫ x in Set.Ioc a b, ‖g x - g b‖ ^ 2
      ≤ (b - a) ^ 2 * ∫ x in Set.Ioc a b, ‖deriv (g : ℝ → ℂ) x‖ ^ 2 := by
  have hc := deriv_continuous g
  set K : ℝ := ∫ x in Set.Ioc a b, ‖deriv (g : ℝ → ℂ) x‖ ^ 2 with hK
  have hint2 : IntegrableOn (fun x => ‖deriv (g : ℝ → ℂ) x‖ ^ 2) (Set.Ioc a b) := by
    simpa using (hc.norm.pow 2).integrableOn_Ioc
  have hbound : ∀ x ∈ Set.Ioc a b, ‖g x - g b‖ ^ 2 ≤ (b - a) * K := by
    intro x hx
    have hxb : x ≤ b := hx.2
    have hax : a ≤ x := le_of_lt hx.1
    have h1 := norm_sub_sq_le g hxb
    rw [← norm_neg, neg_sub] at h1
    set J : ℝ := ∫ t in Set.Ioc x b, ‖deriv (g : ℝ → ℂ) t‖ ^ 2 with hJ
    have hsub : J ≤ K := by
      refine setIntegral_mono_set hint2 ?_ ?_
      · exact Filter.Eventually.of_forall fun _ => by positivity
      · exact Filter.Eventually.of_forall (Set.Ioc_subset_Ioc_left hax)
    have hJ0 : 0 ≤ J := integral_nonneg fun _ => by positivity
    nlinarith [h1, hsub, hJ0, hxb, hax]
  have hintL : IntegrableOn (fun x => ‖g x - g b‖ ^ 2) (Set.Ioc a b) :=
    ((g.continuous.sub continuous_const).norm.pow 2).integrableOn_Ioc
  have hmono := setIntegral_mono_on hintL (integrableOn_const (by simp [Real.volume_Ioc]))
    measurableSet_Ioc hbound
  rw [setIntegral_const] at hmono
  have hm : (volume.real (Set.Ioc a b)) = b - a := by
    simp [Measure.real, Real.volume_Ioc, ENNReal.toReal_ofReal (by linarith : (0:ℝ) ≤ b - a)]
  rw [hm, smul_eq_mul] at hmono
  calc ∫ x in Set.Ioc a b, ‖g x - g b‖ ^ 2 ≤ (b - a) * ((b - a) * K) := hmono
    _ = (b - a) ^ 2 * K := by ring

/-! ### Cells, step functions, and their `L²` classes -/

/-- The `j`-th cell of the partition of `(-R, -R + n·h]` into intervals of
length `h`. -/
