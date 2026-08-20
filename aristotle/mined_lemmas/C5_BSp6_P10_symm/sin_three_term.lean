import Mathlib
open Matrix Polynomial
namespace C5.BSp6

lemma sin_three_term (a : ℝ) :
    Real.sin (a * (Real.pi / 11)) + Real.sin ((a + 2) * (Real.pi / 11))
      = 2 * Real.cos (Real.pi / 11) * Real.sin ((a + 1) * (Real.pi / 11)) := by
  have h1 : a * (Real.pi / 11) = (a + 1) * (Real.pi / 11) - (Real.pi / 11) := by ring
  have h2 : (a + 2) * (Real.pi / 11) = (a + 1) * (Real.pi / 11) + (Real.pi / 11) := by ring
  rw [h1, h2, Real.sin_sub, Real.sin_add]; ring

