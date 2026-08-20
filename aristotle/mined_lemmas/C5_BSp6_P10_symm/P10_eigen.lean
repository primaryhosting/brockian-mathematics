import Mathlib
open Matrix Polynomial
namespace C5.BSp6

theorem P10_eigen : P10.charpoly.eval (2 - 2*Real.cos (Real.pi/11)) = 0 := by
  rw [Matrix.eval_charpoly, ← Matrix.exists_mulVec_eq_zero_iff]
  exact ⟨v10, v10_ne_zero, mulVec_eq_zero⟩

