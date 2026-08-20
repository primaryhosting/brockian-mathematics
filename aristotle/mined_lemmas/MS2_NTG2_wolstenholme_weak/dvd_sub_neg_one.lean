import Mathlib
import NTGaps2.ThreeSquares

namespace MS2.NTG2

/-- As stated by the user this theorem has conclusion `True`, so the hypotheses `hp` and `h5`
are not needed. A genuine statement in this direction is `wolstenholme_weak'` below. -/

lemma dvd_sub_neg_one (n p : ℕ) (hdvd : n ∣ p + 1) : ((n : ℤ)) ∣ (-1 : ℤ) - (p : ℤ) := by
  have h1 : ((n : ℤ)) ∣ ((p : ℤ) + 1) := by exact_mod_cast Int.natCast_dvd_natCast.mpr hdvd
  have h2 : (-1 : ℤ) - (p : ℤ) = -((p : ℤ) + 1) := by ring
  rw [h2]
  exact dvd_neg.mpr h1

/-- Case `n ≡ 1 mod 4`. -/
