import Mathlib
import NTGaps2.ThreeSquares

namespace MS2.NTG2

/-- As stated by the user this theorem has conclusion `True`, so the hypotheses `hp` and `h5`
are not needed. A genuine statement in this direction is `wolstenholme_weak'` below. -/

lemma Q3_complete_square {G : Matrix (Fin 3) (Fin 3) ℤ} (hsym : G.IsSymm) (v : Fin 3 → ℤ) :
    G 0 0 * Q3 G v =
      (G 0 0 * v 0 + G 0 1 * v 1 + G 0 2 * v 2) ^ 2 +
        qb (G 0 0 * G 1 1 - G 0 1 ^ 2) (2 * (G 0 0 * G 1 2 - G 0 2 * G 0 1))
          (G 0 0 * G 2 2 - G 0 2 ^ 2) (v 1) (v 2) := by
  have h10 : G 1 0 = G 0 1 := hsym.apply 0 1
  have h20 : G 2 0 = G 0 2 := hsym.apply 0 2
  have h21 : G 2 1 = G 1 2 := hsym.apply 1 2
  rw [Q3_expand, h10, h20, h21]
  unfold qb
  ring

/-- The discriminant of the binary form obtained by completing the square. -/
