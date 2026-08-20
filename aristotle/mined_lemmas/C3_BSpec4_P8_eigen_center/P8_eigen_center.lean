import Mathlib
open Matrix Polynomial
namespace C3.BSpec4

theorem P8_eigen_center : P8.charpoly.eval (2 - 2*Real.cos (Real.pi/9)) = 0 := by
  rw [Matrix.eval_charpoly]
  exact Matrix.exists_mulVec_eq_zero_iff.mp ⟨eigvec8, eigvec8_ne_zero, P8_mulVec_eigvec8⟩

