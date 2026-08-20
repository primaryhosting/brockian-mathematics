import Mathlib
namespace Brockian.MsHermiteHadamard

open MeasureTheory Set

/-- A convex function on `[a,b]` is bounded above by the max of its values at the endpoints. -/

lemma hh_midpoint {f : ℝ → ℝ} {a b : ℝ} (hf : ConvexOn ℝ (Set.Icc a b) f)
    {x : ℝ} (hx : x ∈ Set.Icc a b) :
    2 * f ((a + b) / 2) ≤ f x + f (a + b - x) := by
  -- First show that a + b - x is also in [a, b]
  have hx'_mem : a + b - x ∈ Set.Icc a b := ⟨by linarith [hx.1, hx.2], by linarith [hx.1, hx.2]⟩
  -- Use convexity with equal weights 1/2 and 1/2
  have hconv := hf.2 hx hx'_mem (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num)
  -- hconv : f(1/2 * x + 1/2 * (a+b-x)) ≤ 1/2 * f(x) + 1/2 * f(a+b-x)
  simp only [smul_eq_mul] at hconv
  calc 2 * f ((a + b) / 2) = 2 * f ((x + (a + b - x)) / 2) := by ring_nf
    _ = 2 * f (1/2 * x + 1/2 * (a + b - x)) := by ring_nf
    _ ≤ 2 * ((1/2) * f x + (1/2) * f (a + b - x)) := by nlinarith
    _ = f x + f (a + b - x) := by ring

/-- A convex function on `[a,b]` is bounded below on `[a,b]`. -/
