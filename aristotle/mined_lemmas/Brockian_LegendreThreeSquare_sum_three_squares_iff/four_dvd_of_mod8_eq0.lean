import Mathlib
import GeometryOfNumbers.Legendre.Main
namespace Brockian.LegendreThreeSquare
/-- Legendre's three-square theorem: n is a sum of three squares iff n is NOT of the
    form 4^a·(8b+7). -/

private lemma four_dvd_of_mod8_eq0 (t : ℕ) (ht0 : t % 8 = 0) : 4 ∣ t := by
  have h8 : 8 ∣ t := Nat.dvd_of_mod_eq_zero ht0
  exact dvd_trans (by exact ⟨2, rfl⟩) h8

