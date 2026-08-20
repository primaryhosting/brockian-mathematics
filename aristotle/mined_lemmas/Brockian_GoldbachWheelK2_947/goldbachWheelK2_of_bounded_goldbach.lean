/-
Primality certificates for the primes occurring in the level-2 Goldbach wheel
witness table for the modulus `947`.

These are auxiliary facts used by `Brockian.GoldbachWheelK2_947`.
-/
import Mathlib.Tactic.NormNum.Prime

namespace Brockian.Wheel


theorem goldbachWheelK2_of_bounded_goldbach {m : ℕ} (hm : Nat.Prime m) (hm2 : 2 < m)
    (h : ∀ n : ℕ, n % 2 = 0 → 4 ≤ n → n ≤ 2 * m →
      ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p + q = n) :
    GoldbachWheelK2 m := by
  intro r hr
  have hmodd : m % 2 = 1 := Nat.odd_iff.mp (hm.odd_of_ne_two (by omega))
  rcases Nat.eq_zero_or_pos r with rfl | hr0
  · refine ⟨m, m, hm, hm, by omega, ?_⟩
    simp [Nat.mod_self]
  · by_cases hpar : r % 2 = 1
    · -- `r` is odd, so `r + m` is even and lies in the Goldbach range
      obtain ⟨p, q, hp, hq, hpq⟩ := h (r + m) (by omega) (by omega) (by omega)
      exact ⟨p, q, hp, hq, by omega, by rw [hpq, Nat.add_mod_right, Nat.mod_eq_of_lt hr]⟩
    · rcases eq_or_lt_of_le (show 2 ≤ r by omega) with hr2 | hr4
      · -- `r = 2`, use the pair `(2, m)`
        refine ⟨2, m, Nat.prime_two, hm, by omega, ?_⟩
        rw [← hr2, Nat.add_mod_right, Nat.mod_eq_of_lt hm2]
      · -- `r` is even and at least `4`
        obtain ⟨p, q, hp, hq, hpq⟩ := h r (by omega) (by omega) (by omega)
        exact ⟨p, q, hp, hq, by omega, by rw [hpq, Nat.mod_eq_of_lt hr]⟩

/-- The smallest member of the family: `5` is a level-2 Goldbach wheel modulus. -/
