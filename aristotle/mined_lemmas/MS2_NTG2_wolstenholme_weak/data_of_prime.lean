import Mathlib
import NTGaps2.ThreeSquares

namespace MS2.NTG2

/-- As stated by the user this theorem has conclusion `True`, so the hypotheses `hp` and `h5`
are not needed. A genuine statement in this direction is `wolstenholme_weak'` below. -/

lemma data_of_prime (n p : ℕ) [Fact p.Prime] (hdvd : n ∣ p + 1)
    (hsign : legendreSym p (-1) * legendreSym p (n : ℤ) = 1) :
    ∃ u M s : ℤ, 0 < M ∧ (n : ℤ) * (u * M - s ^ 2) - M = 1 := by
  have hp : p.Prime := Fact.out
  obtain ⟨D, hD⟩ : ((n : ℤ)) ∣ ((p : ℤ) + 1) := by exact_mod_cast Int.natCast_dvd_natCast.mpr hdvd
  have hmod : ((n : ℤ) * D) % p = 1 % p := by
    rw [← hD]
    have : ((p : ℤ) + 1) ≡ 1 [ZMOD (p : ℤ)] := Int.modEq_iff_dvd.mpr ⟨-1, by ring⟩
    exact this
  obtain ⟨s, hs⟩ := sq_mod_prime p D (D_nonzero p n D hmod) (legendre_neg_D p n D hmod hsign)
  exact data_of_dvd n (p : ℤ) D s (by exact_mod_cast hp.pos) hD.symm hs

/-- The case `M = 2p`. -/
