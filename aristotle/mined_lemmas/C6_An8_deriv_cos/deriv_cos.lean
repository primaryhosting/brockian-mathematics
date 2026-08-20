import Mathlib
namespace C6.An8

/-- The derivative of `cos` is `-sin`. -/

theorem deriv_cos (x : ℝ) : deriv Real.cos x = -Real.sin x := Real.deriv_cos

/-- The Pythagorean identity `sin² x + cos² x = 1`. -/
