import Mathlib
import NTGaps2.ThreeSquares

namespace MS2.NTG2

/-- As stated by the user this theorem has conclusion `True`, so the hypotheses `hp` and `h5`
are not needed. A genuine statement in this direction is `wolstenholme_weak'` below. -/

lemma D_nonzero (p n : ℕ) [Fact p.Prime] (D : ℤ) (hmod : ((n : ℤ) * D) % p = 1 % p) :
    ((-D : ℤ) : ZMod p) ≠ 0 := by
  intro h
  rw [Int.cast_neg, neg_eq_zero, ZMod.intCast_zmod_eq_zero_iff_dvd] at h
  have hdvd : ((p : ℤ)) ∣ (n : ℤ) * D := Dvd.dvd.mul_left h _
  have h0 : ((n : ℤ) * D) % p = 0 := Int.emod_eq_zero_of_dvd hdvd
  rw [h0] at hmod
  have hp := Fact.out (p := p.Prime)
  have h2 : 2 ≤ p := hp.two_le
  have h1 : (1 : ℤ) % (p : ℤ) = 1 := by
    apply Int.emod_eq_of_lt <;> [omega; exact_mod_cast h2]
  omega

/-- The case `M = p`. -/
