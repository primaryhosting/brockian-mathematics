import Mathlib
import NTGaps2.ThreeSquares

namespace MS2.NTG2

/-- As stated by the user this theorem has conclusion `True`, so the hypotheses `hp` and `h5`
are not needed. A genuine statement in this direction is `wolstenholme_weak'` below. -/

lemma Q3_smul (G : Matrix (Fin 3) (Fin 3) ℤ) (d : ℤ) (v : Fin 3 → ℤ) :
    Q3 G (fun i => d * v i) = d ^ 2 * Q3 G v := by
  rw [Q3_expand, Q3_expand]; ring

