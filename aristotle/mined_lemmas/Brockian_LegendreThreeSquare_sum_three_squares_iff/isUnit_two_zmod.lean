import Mathlib
import GeometryOfNumbers.Legendre.Main
namespace Brockian.LegendreThreeSquare
/-- Legendre's three-square theorem: n is a sum of three squares iff n is NOT of the
    form 4^a·(8b+7). -/

lemma isUnit_two_zmod (n : ℕ) (hn : n % 2 = 1) : IsUnit (2 : ZMod n) := by
  apply (ZMod.isUnit_iff_coprime 2 n).mpr
  apply (Nat.prime_two.coprime_iff_not_dvd).mpr
  intro h
  have : n % 2 = 0 := Nat.dvd_iff_mod_eq_zero.mp h
  rw [hn] at this
  contradiction

/-- Every `n` can be written as `s^2 * m` where `m` is squarefree. -/
