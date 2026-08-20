import Mathlib
import NTGaps2.ThreeSquares

namespace MS2.NTG2

/-- As stated by the user this theorem has conclusion `True`, so the hypotheses `hp` and `h5`
are not needed. A genuine statement in this direction is `wolstenholme_weak'` below. -/

lemma symbol_even (n' p : ℕ) [Fact p.Prime] (hn' : Odd n') (hp4 : p % 4 = 1)
    (hdvd : n' ∣ p + 1) :
    legendreSym p (2 * (n' : ℤ)) = ZMod.χ₈ (p : ℕ) * ZMod.χ₄ (n' : ℕ) := by
  have hpodd : Odd p := Nat.odd_iff.mpr (by omega)
  rw [jacobiSym.legendreSym.to_jacobiSym, jacobiSym.mul_left, jacobiSym.at_two hpodd,
    jacobiSym.quadratic_reciprocity_one_mod_four' hn' hp4,
    jacobiSym.mod_left' (Int.modEq_iff_dvd.mpr (dvd_sub_neg_one n' p hdvd)),
    jacobiSym.at_neg_one hn']

/-! ### Choosing the prime -/

