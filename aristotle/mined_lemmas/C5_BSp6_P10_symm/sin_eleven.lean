import Mathlib
open Matrix Polynomial
namespace C5.BSp6

lemma sin_eleven : Real.sin (11 * (Real.pi / 11)) = 0 := by
  have h : (11 : ℝ) * (Real.pi / 11) = Real.pi := by ring
  rw [h, Real.sin_pi]

