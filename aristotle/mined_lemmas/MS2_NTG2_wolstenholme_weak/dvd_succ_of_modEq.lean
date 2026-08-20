import Mathlib
import NTGaps2.ThreeSquares

namespace MS2.NTG2

/-- As stated by the user this theorem has conclusion `True`, so the hypotheses `hp` and `h5`
are not needed. A genuine statement in this direction is `wolstenholme_weak'` below. -/

lemma dvd_succ_of_modEq {p r n k : ℕ} (hnk : n ∣ k) (hpr : p ≡ r [MOD k]) (h : n ∣ r + 1) :
    n ∣ p + 1 :=
  Nat.modEq_zero_iff_dvd.mp
    (((Nat.ModEq.of_dvd hnk hpr).add_right 1).trans (Nat.modEq_zero_iff_dvd.mpr h))

/-- Transfer of a congruence for `p` to the divisibility `n ∣ 2p + 1`. -/
