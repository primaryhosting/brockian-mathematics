import Mathlib
import NTGaps2.ThreeSquares

namespace MS2.NTG2

/-- As stated by the user this theorem has conclusion `True`, so the hypotheses `hp` and `h5`
are not needed. A genuine statement in this direction is `wolstenholme_weak'` below. -/

lemma coprime_two_pow_of_odd {r : ℕ} (h : r % 2 = 1) (k : ℕ) : Nat.Coprime r (2 ^ k) :=
  Nat.Coprime.pow_right k
    (Nat.coprime_comm.mp ((Nat.prime_two.coprime_iff_not_dvd).mpr (by omega)))

/-- Transfer of a congruence for `p` to the divisibility `n ∣ p + 1`. -/
