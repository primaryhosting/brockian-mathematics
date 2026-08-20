import Mathlib
import NTGaps2.ThreeSquares

namespace MS2.NTG2

/-- As stated by the user this theorem has conclusion `True`, so the hypotheses `hp` and `h5`
are not needed. A genuine statement in this direction is `wolstenholme_weak'` below. -/

theorem legendre_three_square (n : ℕ) (h : ¬ ∃ a b : ℕ, n = 4^a*(8*b+7)) :
    ∃ x y z : ℕ, x^2+y^2+z^2 = n :=
  ThreeSquares.nat_sum_three_squares n h

/-- Squares are `0` or `1` mod `4`, with the parity of the base recorded. -/
