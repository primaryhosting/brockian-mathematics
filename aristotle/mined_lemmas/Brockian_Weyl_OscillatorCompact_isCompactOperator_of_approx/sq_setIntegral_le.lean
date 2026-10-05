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

theorem sq_setIntegral_le {I : Set ℝ} (f : ℝ → ℝ)
    (hf : IntegrableOn f I) (hf2 : IntegrableOn (fun x => f x ^ 2) I)
    (hfin : volume I ≠ ⊤) :
    (∫ x in I, f x) ^ 2 ≤ (volume.real I) * ∫ x in I, f x ^ 2 := by
  set m := volume.real I with hm
  have hm0 : 0 ≤ m := by positivity
  rcases eq_or_lt_of_le hm0 with hmz | hmpos
  · have hz : volume I = 0 := by
      have h : (volume I).toReal = 0 := hmz.symm
      exact ((ENNReal.toReal_eq_zero_iff _).mp h).resolve_right hfin
    have h1 : ∫ x in I, f x = 0 := by
      rw [Measure.restrict_eq_zero.mpr hz]; simp
    have h2 : ∫ x in I, f x ^ 2 = 0 := by
      rw [Measure.restrict_eq_zero.mpr hz]; simp
    rw [h1, h2]; simp
  · set t := (∫ x in I, f x) / m with ht
    have hconst : IntegrableOn (fun _ : ℝ => t ^ 2) I := integrableOn_const hfin
    have hlin : IntegrableOn (fun x => f x ^ 2 - 2 * t * f x) I :=
      hf2.sub (hf.const_mul (2 * t))
    have hkey : 0 ≤ ∫ x in I, (f x - t) ^ 2 := by
      apply integral_nonneg; intro x; positivity
    have hexp : ∫ x in I, (f x - t) ^ 2
        = (∫ x in I, f x ^ 2) - 2 * t * (∫ x in I, f x) + t ^ 2 * m := by
      have hpt : ∀ x, (f x - t) ^ 2 = (f x ^ 2 - (2 * t) * f x) + t ^ 2 := by intro x; ring
      simp only [hpt]
      rw [integral_add hlin hconst, integral_sub hf2 (hf.const_mul (2 * t)),
        integral_const_mul]
      simp [hm, mul_comm]
    rw [hexp] at hkey
    have hmne : m ≠ 0 := ne_of_gt hmpos
    have htm : t * m = ∫ x in I, f x := div_mul_cancel₀ _ hmne
    nlinarith [hkey, htm]

/-! ### The one-dimensional Poincaré estimate on a cell -/

/-- The derivative of a Schwartz function is continuous. -/
