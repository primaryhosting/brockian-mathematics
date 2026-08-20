import Mathlib
open Matrix
namespace MS.LogicQuantum


theorem no_cloning (z : ℂ) (h : z = z ^ 2) : z = 0 ∨ z = 1 := by
  have h' : z * (z - 1) = 0 := by linear_combination -h
  rcases mul_eq_zero.mp h' with h0 | h1
  · exact Or.inl h0
  · exact Or.inr (sub_eq_zero.mp h1)

/-- Robertson uncertainty seed: Pauli X,Z anticommute so cannot be simultaneously ±1-definite. -/
