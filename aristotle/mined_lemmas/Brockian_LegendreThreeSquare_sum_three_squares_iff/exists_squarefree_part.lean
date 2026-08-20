import Mathlib
import GeometryOfNumbers.Legendre.Main
namespace Brockian.LegendreThreeSquare
/-- Legendre's three-square theorem: n is a sum of three squares iff n is NOT of the
    form 4^a·(8b+7). -/

lemma exists_squarefree_part (n : ℕ) :
    ∃ s m : ℕ, n = s^2 * m ∧ Squarefree m := by
  obtain ⟨m, s, h_eq, h_sq⟩ := Nat.sq_mul_squarefree n
  use s, m
  constructor
  · rw [h_eq]
  · exact h_sq

/-- If `n ≡ 3 (mod 8)`, then its squarefree part `m` satisfies `m ≡ 3 (mod 8)`. -/
