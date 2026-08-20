import Mathlib
import NTGaps2.ThreeSquares

namespace MS2.NTG2

/-- As stated by the user this theorem has conclusion `True`, so the hypotheses `hp` and `h5`
are not needed. A genuine statement in this direction is `wolstenholme_weak'` below. -/

lemma Q3_congr (G U : Matrix (Fin 3) (Fin 3) ℤ) (v : Fin 3 → ℤ) :
    Q3 (Uᵀ * G * U) v = Q3 G (U *ᵥ v) := by
  simp only [Q3, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]

