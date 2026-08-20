import Mathlib
import NTGaps2.ThreeSquares

namespace MS2.NTG2

/-- As stated by the user this theorem has conclusion `True`, so the hypotheses `hp` and `h5`
are not needed. A genuine statement in this direction is `wolstenholme_weak'` below. -/

lemma legendre_neg_D (p n : ℕ) [Fact p.Prime] (D : ℤ) (hmod : ((n : ℤ) * D) % p = 1 % p)
    (hsign : legendreSym p (-1) * legendreSym p (n : ℤ) = 1) : legendreSym p (-D) = 1 := by
  have h1 : legendreSym p ((n : ℤ) * D) = 1 := by
    rw [legendreSym.mod, hmod, ← legendreSym.mod, legendreSym.at_one]
  rw [legendreSym.mul] at h1
  have hneg : legendreSym p (-D) = legendreSym p (-1) * legendreSym p D := by
    rw [← legendreSym.mul]; norm_num
  rcases Int.eq_one_or_neg_one_of_mul_eq_one h1 with h | h
  · have h2 : legendreSym p (-1) = 1 := by rw [h] at hsign; linarith
    have h3 : legendreSym p D = 1 := by rw [h] at h1; linarith
    rw [hneg, h2, h3]; ring
  · have h2 : legendreSym p (-1) = -1 := by rw [h] at hsign; linarith
    have h3 : legendreSym p D = -1 := by rw [h] at h1; linarith
    rw [hneg, h2, h3]; ring

