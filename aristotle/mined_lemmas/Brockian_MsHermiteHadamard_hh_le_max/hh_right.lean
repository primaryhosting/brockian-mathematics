import Mathlib
namespace Brockian.MsHermiteHadamard

open MeasureTheory Set

/-- A convex function on `[a,b]` is bounded above by the max of its values at the endpoints. -/

lemma hh_right {f : ℝ → ℝ} {a b : ℝ} (hab : a < b) (hf : ConvexOn ℝ (Set.Icc a b) f) :
    (∫ x in a..b, f x) ≤ (b - a) * ((f a + f b) / 2) := by
  have hint := hh_integrable hab hf
  have hba : b - a ≠ 0 := by linarith
  set C : ℝ := f a - a * (f b - f a) / (b - a) with hC
  set D : ℝ := (f b - f a) / (b - a) with hD
  have hfun : (fun x : ℝ => f a + (x - a) / (b - a) * (f b - f a)) = fun x : ℝ => C + x * D := by
    funext x
    rw [hC, hD]
    field_simp
    ring
  have hg : IntervalIntegrable (fun x : ℝ => f a + (x - a) / (b - a) * (f b - f a)) volume a b := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hmono := intervalIntegral.integral_mono_on hab.le hint hg (fun x hx => hh_le_chord hab hf hx)
  have hcalc : (∫ x in a..b, (f a + (x - a) / (b - a) * (f b - f a)))
      = (b - a) * ((f a + f b) / 2) := by
    rw [hfun, intervalIntegral.integral_add _root_.intervalIntegrable_const
      (intervalIntegral.intervalIntegrable_id.mul_const D)]
    simp [intervalIntegral.integral_mul_const, integral_id, hC, hD]
    field_simp
    ring
  linarith [hcalc ▸ hmono]

/-- The left-hand Hermite–Hadamard inequality, in unnormalized form. -/
