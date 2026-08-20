import Mathlib
import NTGaps2.ThreeSquares

namespace MS2.NTG2

/-- As stated by the user this theorem has conclusion `True`, so the hypotheses `hp` and `h5`
are not needed. A genuine statement in this direction is `wolstenholme_weak'` below. -/

lemma isSymm_congr {G : Matrix (Fin 3) (Fin 3) ℤ} (hsym : G.IsSymm)
    (U : Matrix (Fin 3) (Fin 3) ℤ) : (Uᵀ * G * U).IsSymm := by
  unfold Matrix.IsSymm
  rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, hsym.eq,
    Matrix.mul_assoc]

/-- A vector is nonzero iff one of its three coordinates is. -/
