import Mathlib
import NTGaps2.ThreeSquares

namespace MS2.NTG2

/-- As stated by the user this theorem has conclusion `True`, so the hypotheses `hp` and `h5`
are not needed. A genuine statement in this direction is `wolstenholme_weak'` below. -/

lemma symbol_one_mod_four (n p : ℕ) [Fact p.Prime] (hn4 : n % 4 = 1) (hp4 : p % 4 = 1)
    (hdvd : n ∣ p + 1) : legendreSym p (-1) * legendreSym p (n : ℤ) = 1 := by
  have hp2 : p ≠ 2 := by omega
  have hnodd : Odd n := Nat.odd_iff.mpr (by omega)
  have h1 : legendreSym p (-1) = 1 := by
    rw [legendreSym.at_neg_one hp2, ZMod.χ₄_nat_one_mod_four hp4]
  have h3 : jacobiSym (p : ℤ) n = jacobiSym (-1 : ℤ) n :=
    jacobiSym.mod_left' (Int.modEq_iff_dvd.mpr (dvd_sub_neg_one n p hdvd))
  rw [h1, one_mul, jacobiSym.legendreSym.to_jacobiSym,
    jacobiSym.quadratic_reciprocity_one_mod_four' hnodd hp4, h3, jacobiSym.at_neg_one hnodd,
    ZMod.χ₄_nat_one_mod_four hn4]

/-- Case `n ≡ 3 mod 8`. -/
