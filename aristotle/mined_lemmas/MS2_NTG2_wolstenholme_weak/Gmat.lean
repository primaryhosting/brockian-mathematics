import Mathlib
import NTGaps2.ThreeSquares

namespace MS2.NTG2

/-- As stated by the user this theorem has conclusion `True`, so the hypotheses `hp` and `h5`
are not needed. A genuine statement in this direction is `wolstenholme_weak'` below. -/

def Gmat (n u M s : ℤ) : Matrix (Fin 3) (Fin 3) ℤ := !![n, 1, 0; 1, u, -s; 0, -s, M]

