import Mathlib
import GeometryOfNumbers.Legendre.Main
namespace Brockian.LegendreThreeSquare
/-- Legendre's three-square theorem: n is a sum of three squares iff n is NOT of the
    form 4^a·(8b+7). -/

lemma coprime_four_n (n : ℕ) (hn : n % 2 = 1) : Nat.Coprime 4 n := by
  have h2 : Nat.Coprime 2 n := by
    apply (Nat.prime_two.coprime_iff_not_dvd).mpr
    intro h
    have : n % 2 = 0 := Nat.dvd_iff_mod_eq_zero.mp h
    rw [hn] at this
    contradiction
  show Nat.Coprime (2^2) n
  apply Nat.Coprime.pow_left 2 h2

/-- 2 is invertible modulo any odd n. -/
