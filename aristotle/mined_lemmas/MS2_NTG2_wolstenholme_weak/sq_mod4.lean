import Mathlib
import NTGaps2.ThreeSquares

namespace MS2.NTG2

/-- As stated by the user this theorem has conclusion `True`, so the hypotheses `hp` and `h5`
are not needed. A genuine statement in this direction is `wolstenholme_weak'` below. -/

private lemma sq_mod4 (x : ℕ) : (x^2 % 4 = 0 ∧ x % 2 = 0) ∨ (x^2 % 4 = 1 ∧ x % 2 = 1) := by
  rcases Nat.even_or_odd x with ⟨k, hk⟩ | ⟨k, hk⟩
  · left; subst hk; refine ⟨?_, by omega⟩
    have : (k + k)^2 = 4 * k^2 := by ring
    omega
  · right; subst hk; refine ⟨?_, by omega⟩
    have : (2*k+1)^2 = 4 * (k^2+k) + 1 := by ring
    omega

