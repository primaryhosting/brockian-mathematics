import Mathlib
namespace Brockian.MsHermiteHadamard

open MeasureTheory Set

/-- A convex function on `[a,b]` is bounded above by the max of its values at the endpoints. -/

lemma hh_left {f : ℝ → ℝ} {a b : ℝ} (hab : a < b) (hf : ConvexOn ℝ (Set.Icc a b) f) :
    (b - a) * f ((a + b) / 2) ≤ ∫ x in a..b, f x := by
  have hint := hh_integrable hab hf
  have hrefl : (∫ x in a..b, f (a + b - x)) = ∫ x in a..b, f x := by
    simp
  have hint2 : IntervalIntegrable (fun x => f (a + b - x)) volume a b := by
    have := (hint.comp_sub_left (a + b)).symm
    simpa using this
  have hmono : (∫ _x in a..b, 2 * f ((a + b) / 2)) ≤ ∫ x in a..b, (f x + f (a + b - x)) := by
    apply intervalIntegral.integral_mono_on hab.le (by simp) (hint.add hint2)
    intro x hx
    exact hh_midpoint hf hx
  rw [intervalIntegral.integral_add hint hint2, hrefl] at hmono
  simp at hmono
  linarith

/-- The Hermite–Hadamard inequality: for a convex f on [a,b] with a < b,
    f((a+b)/2) ≤ (1/(b−a)) ∫_a^b f ≤ (f a + f b)/2. -/
