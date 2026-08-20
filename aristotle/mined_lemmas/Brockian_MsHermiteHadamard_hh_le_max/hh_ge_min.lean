import Mathlib
namespace Brockian.MsHermiteHadamard

open MeasureTheory Set

/-- A convex function on `[a,b]` is bounded above by the max of its values at the endpoints. -/

lemma hh_ge_min {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b) (hf : ConvexOn ℝ (Set.Icc a b) f)
    {x : ℝ} (hx : x ∈ Set.Icc a b) :
    2 * f ((a + b) / 2) - max (f a) (f b) ≤ f x := by
  have h1 := hh_midpoint hf hx
  have hx' : a + b - x ∈ Set.Icc a b := ⟨by linarith [hx.1, hx.2], by linarith [hx.1, hx.2]⟩
  have h2 := hh_le_max hab hf hx'
  linarith

/-- A convex function on `[a,b]` is interval integrable there. -/
