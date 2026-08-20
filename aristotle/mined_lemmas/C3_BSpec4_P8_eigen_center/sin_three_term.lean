import Mathlib
open Matrix Polynomial
namespace C3.BSpec4

private lemma sin_three_term (a : ℝ) :
    Real.sin (a - Real.pi / 9) - Real.cos (Real.pi / 9) * Real.sin a * 2
      + Real.sin (a + Real.pi / 9) = 0 := by
  rw [Real.sin_add, Real.sin_sub]; ring

