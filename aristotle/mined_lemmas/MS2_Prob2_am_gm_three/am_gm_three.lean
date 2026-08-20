import Mathlib
open Finset
namespace MS2.Prob2

/-- AM–GM for three nonnegative reals. -/

theorem am_gm_three (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    (a*b*c)^((1:ℝ)/3) ≤ (a+b+c)/3 := by
  have h := Real.geom_mean_le_arith_mean3_weighted
    (w₁ := 1/3) (w₂ := 1/3) (w₃ := 1/3) (p₁ := a) (p₂ := b) (p₃ := c)
    (by norm_num) (by norm_num) (by norm_num) ha hb hc (by norm_num)
  calc (a*b*c)^((1:ℝ)/3) = a^((1:ℝ)/3) * b^((1:ℝ)/3) * c^((1:ℝ)/3) := by
        rw [Real.mul_rpow (mul_nonneg ha hb) hc, Real.mul_rpow ha hb]
    _ ≤ 1/3 * a + 1/3 * b + 1/3 * c := h
    _ = (a+b+c)/3 := by ring

/-- The two-element rearrangement inequality. -/
