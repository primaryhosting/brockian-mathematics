import Mathlib
import NTGaps2.ThreeSquares

namespace MS2.NTG2

/-- As stated by the user this theorem has conclusion `True`, so the hypotheses `hp` and `h5`
are not needed. A genuine statement in this direction is `wolstenholme_weak'` below. -/

lemma qb_smul (A B C g x y : ℤ) : qb A B C (g * x) (g * y) = g ^ 2 * qb A B C x y := by
  unfold qb; ring

/-- Existence of a minimal nonzero value of a positive definite binary form. -/
