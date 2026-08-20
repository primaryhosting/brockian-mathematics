import Mathlib
import NTGaps2.ThreeSquares

namespace MS2.NTG2

/-- As stated by the user this theorem has conclusion `True`, so the hypotheses `hp` and `h5`
are not needed. A genuine statement in this direction is `wolstenholme_weak'` below. -/

lemma four_mul_qb (A B C x y : ℤ) :
    4 * A * qb A B C x y = (2 * A * x + B * y) ^ 2 + (4 * A * C - B ^ 2) * y ^ 2 := by
  unfold qb; ring

/-- A positive definite binary form takes positive values on nonzero vectors. -/
