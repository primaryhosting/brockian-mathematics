import Mathlib
namespace C5.An7

theorem deriv_sin (x : ℝ) : deriv Real.sin x = Real.cos x := Real.deriv_sin ▸ rfl
