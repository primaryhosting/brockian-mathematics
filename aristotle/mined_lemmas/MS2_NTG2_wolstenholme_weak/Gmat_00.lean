import Mathlib
import NTGaps2.ThreeSquares

namespace MS2.NTG2

/-- As stated by the user this theorem has conclusion `True`, so the hypotheses `hp` and `h5`
are not needed. A genuine statement in this direction is `wolstenholme_weak'` below. -/

@[simp] lemma Gmat_00 (n u M s : ℤ) : Gmat n u M s 0 0 = n := rfl
