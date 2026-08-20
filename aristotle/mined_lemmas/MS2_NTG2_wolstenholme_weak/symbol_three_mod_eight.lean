import Mathlib
import NTGaps2.ThreeSquares

namespace MS2.NTG2

/-- As stated by the user this theorem has conclusion `True`, so the hypotheses `hp` and `h5`
are not needed. A genuine statement in this direction is `wolstenholme_weak'` below. -/

lemma symbol_three_mod_eight (n p : ℕ) [Fact p.Prime] (hn8 : n % 8 = 3) (hp2 : p % 2 = 1)
    (hdvd : n ∣ 2 * p + 1) : legendreSym p (-1) * legendreSym p (n : ℤ) = 1 := by
  have hpne : p ≠ 2 := by omega
  have hnodd : Odd n := Nat.odd_iff.mpr (by omega)
  have hpodd : Odd p := Nat.odd_iff.mpr hp2
  have hcong : jacobiSym ((2 * p : ℕ) : ℤ) n = jacobiSym (-1 : ℤ) n := by
    refine jacobiSym.mod_left' (Int.modEq_iff_dvd.mpr ?_)
    have h1 : ((n : ℤ)) ∣ ((2 * p : ℕ) : ℤ) + 1 := by
      exact_mod_cast Int.natCast_dvd_natCast.mpr hdvd
    have h2 : (-1 : ℤ) - ((2 * p : ℕ) : ℤ) = -(((2 * p : ℕ) : ℤ) + 1) := by ring
    rw [h2]; exact dvd_neg.mpr h1
  rw [jacobiSym.at_neg_one hnodd, ZMod.χ₄_nat_three_mod_four (by omega)] at hcong
  have hsplit : jacobiSym ((2 * p : ℕ) : ℤ) n = jacobiSym 2 n * jacobiSym (p : ℤ) n := by
    push_cast
    exact jacobiSym.mul_left 2 (p : ℤ) n
  rw [hsplit, jacobiSym.at_two hnodd] at hcong
  have hchi8 : ZMod.χ₈ (n : ℕ) = -1 := by
    rw [ZMod.χ₈_nat_eq_if_mod_eight]
    have h1 : n % 2 ≠ 0 := by omega
    have h2 : ¬ (n % 8 = 1 ∨ n % 8 = 7) := by omega
    simp [h1, h2]
  rw [hchi8] at hcong
  have hpn : jacobiSym (p : ℤ) n = 1 := by linarith [hcong]
  have hrec : jacobiSym (n : ℤ) p = (-1) ^ (n / 2 * (p / 2)) * jacobiSym (p : ℤ) n :=
    jacobiSym.quadratic_reciprocity hnodd hpodd
  have hn2 : Odd (n / 2) := Nat.odd_iff.mpr (by omega)
  have hpow : ((-1 : ℤ)) ^ (n / 2 * (p / 2)) = ZMod.χ₄ (p : ℕ) := by
    rw [pow_mul, hn2.neg_one_pow, ZMod.χ₄_eq_neg_one_pow hp2]
  rw [hpn, mul_one, hpow] at hrec
  rw [legendreSym.at_neg_one hpne, jacobiSym.legendreSym.to_jacobiSym, hrec,
    ZMod.χ₄_eq_neg_one_pow hp2, ← pow_add]
  exact Even.neg_one_pow ⟨p / 2, rfl⟩

/-- Case `n = 2n'` with `n'` odd. -/
