import Mathlib
import NTGaps2.ThreeSquares

namespace MS2.NTG2

/-- As stated by the user this theorem has conclusion `True`, so the hypotheses `hp` and `h5`
are not needed. A genuine statement in this direction is `wolstenholme_weak'` below. -/

lemma Q3_e0 (G : Matrix (Fin 3) (Fin 3) ℤ) : Q3 G ![1, 0, 0] = G 0 0 := by
  rw [Q3_expand]; simp

/-- The minimum of a positive definite integral ternary form of determinant `1` is `1`. -/
