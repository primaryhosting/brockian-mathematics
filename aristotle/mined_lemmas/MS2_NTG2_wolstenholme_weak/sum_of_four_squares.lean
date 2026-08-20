import Mathlib
import NTGaps2.ThreeSquares

namespace MS2.NTG2

/-- As stated by the user this theorem has conclusion `True`, so the hypotheses `hp` and `h5`
are not needed. A genuine statement in this direction is `wolstenholme_weak'` below. -/

theorem sum_of_four_squares (n : ℕ) : ∃ a b c d : ℕ, a^2+b^2+c^2+d^2 = n :=
  Nat.sum_four_squares n

