import Mathlib
import GeometryOfNumbers.Legendre.Main
namespace Brockian.LegendreThreeSquare
/-- Legendre's three-square theorem: n is a sum of three squares iff n is NOT of the
    form 4^a·(8b+7). -/

lemma zmod_isUnit_two_of_mod8_eq1 (n : ℕ) (hn : n % 8 = 1) : IsUnit (2 : ZMod n) :=
  zmod_isUnit_two_of_odd n (odd_of_mod8_eq1 hn)

/-- Cast bridge used repeatedly in the Ankeny pipeline:

If `q = -(2)⁻¹` in `ZMod n` (with `n` odd so `2` is a unit), then
\[
  2q \equiv -1 \pmod n
\]
as an `Int.ModEq` statement. -/
