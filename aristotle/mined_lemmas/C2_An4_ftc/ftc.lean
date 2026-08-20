import Mathlib
open intervalIntegral MeasureTheory
namespace C2.An4

/-- Fundamental theorem of calculus: if `F` has derivative `f` everywhere and `f` is
continuous, then `∫ x in a..b, f x = F b - F a`. -/

theorem ftc (f : ℝ → ℝ) (a b : ℝ) (hf : ∀ x, HasDerivAt F (f x) x) (hc : Continuous f) :
    ∫ x in a..b, f x = F b - F a :=
  intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hf x) (hc.intervalIntegrable a b)

/-- The partial sums of a geometric series with ratio `|r| < 1` converge to `1 / (1 - r)`. -/
