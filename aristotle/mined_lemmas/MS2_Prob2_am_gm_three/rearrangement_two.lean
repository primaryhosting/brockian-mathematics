import Mathlib
open Finset
namespace MS2.Prob2

/-- AM–GM for three nonnegative reals. -/

theorem rearrangement_two (a1 a2 b1 b2 : ℝ) (ha : a1 ≤ a2) (hb : b1 ≤ b2) :
    a1*b2 + a2*b1 ≤ a1*b1 + a2*b2 := by
  nlinarith [mul_nonneg (sub_nonneg.mpr ha) (sub_nonneg.mpr hb)]

/-- A sum of squares of reals is nonnegative. -/
