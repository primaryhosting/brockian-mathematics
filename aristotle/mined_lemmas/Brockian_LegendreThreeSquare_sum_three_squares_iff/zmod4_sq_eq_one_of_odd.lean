import Mathlib
import GeometryOfNumbers.Legendre.Main
namespace Brockian.LegendreThreeSquare
/-- Legendre's three-square theorem: n is a sum of three squares iff n is NOT of the
    form 4^a·(8b+7). -/

private lemma zmod4_sq_eq_one_of_odd (x : ℕ) (hx : Odd x) : ((x : ZMod 4) ^ 2) = 1 := by
  rcases hx with ⟨m, rfl⟩
  -- `(2m+1)^2 = 4*(m*(m+1)) + 1`, and `4 = 0` in `ZMod 4`.
  -- First normalize the coercion `(2*m+1 : ℕ) ↦ ZMod 4`.
  have hcast : ((2 * m + 1 : ℕ) : ZMod 4) = (2 * (m : ZMod 4) + 1) := by
    simp [Nat.cast_add, Nat.cast_mul]
  calc
    (((2 * m + 1 : ℕ) : ZMod 4) ^ 2)
        = ((2 * (m : ZMod 4) + 1) ^ 2) := by simp [hcast]
    _ = (4 : ZMod 4) * (m : ZMod 4) * ((m : ZMod 4) + 1) + 1 := by ring
    _ = 1 := by
          -- `4 = 0` in `ZMod 4`.
          have h4 : (4 : ZMod 4) = 0 := by
            simpa using (ZMod.natCast_self 4)
          simp [h4]

