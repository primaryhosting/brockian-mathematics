import Mathlib
import NTGaps2.ThreeSquares

namespace MS2.NTG2

/-- As stated by the user this theorem has conclusion `True`, so the hypotheses `hp` and `h5`
are not needed. A genuine statement in this direction is `wolstenholme_weak'` below. -/

lemma Gmat_isSymm (n u M s : ℤ) : (Gmat n u M s).IsSymm := by
  unfold Matrix.IsSymm Gmat
  ext i j
  fin_cases i <;> fin_cases j <;> simp

