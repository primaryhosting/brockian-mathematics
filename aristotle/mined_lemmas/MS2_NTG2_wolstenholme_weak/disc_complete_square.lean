import Mathlib
import NTGaps2.ThreeSquares

namespace MS2.NTG2

/-- As stated by the user this theorem has conclusion `True`, so the hypotheses `hp` and `h5`
are not needed. A genuine statement in this direction is `wolstenholme_weak'` below. -/

lemma disc_complete_square {G : Matrix (Fin 3) (Fin 3) ℤ} (hsym : G.IsSymm) :
    4 * (G 0 0 * G 1 1 - G 0 1 ^ 2) * (G 0 0 * G 2 2 - G 0 2 ^ 2)
        - (2 * (G 0 0 * G 1 2 - G 0 2 * G 0 1)) ^ 2 = 4 * G 0 0 * G.det := by
  have h10 : G 1 0 = G 0 1 := hsym.apply 0 1
  have h20 : G 2 0 = G 0 2 := hsym.apply 0 2
  have h21 : G 2 1 = G 1 2 := hsym.apply 1 2
  rw [Matrix.det_fin_three, h10, h20, h21]
  ring

/-! ### Completing a primitive vector to a basis -/

