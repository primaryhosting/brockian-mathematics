import Mathlib
import NTGaps2.ThreeSquares

namespace MS2.NTG2

/-- As stated by the user this theorem has conclusion `True`, so the hypotheses `hp` and `h5`
are not needed. A genuine statement in this direction is `wolstenholme_weak'` below. -/

lemma det_congr (G U : Matrix (Fin 3) (Fin 3) ℤ) :
    (Uᵀ * G * U).det = U.det ^ 2 * G.det := by
  simp [Matrix.det_mul]; ring

