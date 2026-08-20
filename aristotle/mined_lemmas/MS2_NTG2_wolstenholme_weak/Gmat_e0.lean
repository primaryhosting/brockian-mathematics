import Mathlib
import NTGaps2.ThreeSquares

namespace MS2.NTG2

/-- As stated by the user this theorem has conclusion `True`, so the hypotheses `hp` and `h5`
are not needed. A genuine statement in this direction is `wolstenholme_weak'` below. -/

lemma Gmat_e0 (n u M s : ℤ) : Q3 (Gmat n u M s) ![1, 0, 0] = n := by
  rw [Q3_e0, Gmat_00]

/-- The matrix is positive definite as soon as `n, M > 0` and its determinant is `1`. -/
