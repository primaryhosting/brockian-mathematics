import Mathlib
open Finset
namespace MS2.IT2

theorem entropy_nonneg (p : ℝ) (h0 : 0 ≤ p) (h1 : p ≤ 1) : 0 ≤ -p * Real.log p := by
  have hlog : Real.log p ≤ 0 := Real.log_nonpos h0 h1
  nlinarith [mul_nonneg h0 (neg_nonneg.mpr hlog)]
