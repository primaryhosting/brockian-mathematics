import Mathlib
import NTGaps2.ThreeSquares

namespace MS2.NTG2

/-- As stated by the user this theorem has conclusion `True`, so the hypotheses `hp` and `h5`
are not needed. A genuine statement in this direction is `wolstenholme_weak'` below. -/

lemma Q3_expand (G : Matrix (Fin 3) (Fin 3) ℤ) (v : Fin 3 → ℤ) :
    Q3 G v = G 0 0 * v 0 ^ 2 + G 1 1 * v 1 ^ 2 + G 2 2 * v 2 ^ 2
      + (G 0 1 + G 1 0) * (v 0 * v 1) + (G 0 2 + G 2 0) * (v 0 * v 2)
      + (G 1 2 + G 2 1) * (v 1 * v 2) := by
  simp [Q3, Matrix.mulVec, dotProduct, Fin.sum_univ_three]; ring

