import Mathlib
import GeometryOfNumbers.Legendre.Main
namespace Brockian.LegendreThreeSquare
/-- Legendre's three-square theorem: n is a sum of three squares iff n is NOT of the
    form 4^a·(8b+7). -/

private lemma descend_four {x y z m : ℕ}
    (h : x ^ 2 + y ^ 2 + z ^ 2 = 4 * m) :
    ∃ x' y' z' : ℕ, x' ^ 2 + y' ^ 2 + z' ^ 2 = m := by
  have hev := even_of_sum_three_squares_eq_mul_four (x := x) (y := y) (z := z) (m := m) h
  rcases hev.1 with ⟨x', rfl⟩
  rcases hev.2.1 with ⟨y', rfl⟩
  rcases hev.2.2 with ⟨z', rfl⟩
  -- Factor out the `4` on the LHS and cancel.
  have hfactor :
      (x' + x') ^ 2 + (y' + y') ^ 2 + (z' + z') ^ 2 = 4 * (x' ^ 2 + y' ^ 2 + z' ^ 2) := by
    -- expand squares and collect `4`
    simp [pow_two]
    ring
  have hmul : 4 * (x' ^ 2 + y' ^ 2 + z' ^ 2) = 4 * m := by
    calc
      4 * (x' ^ 2 + y' ^ 2 + z' ^ 2)
          = (x' + x') ^ 2 + (y' + y') ^ 2 + (z' + z') ^ 2 := by
                exact hfactor.symm
      _ = 4 * m := by exact h
  have hcancel : x' ^ 2 + y' ^ 2 + z' ^ 2 = m :=
    Nat.mul_left_cancel (show 0 < 4 from by decide) hmul
  exact ⟨x', y', z', hcancel⟩

