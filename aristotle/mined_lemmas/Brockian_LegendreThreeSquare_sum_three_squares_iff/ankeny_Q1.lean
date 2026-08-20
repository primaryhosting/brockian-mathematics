import Mathlib
import GeometryOfNumbers.Legendre.Main
namespace Brockian.LegendreThreeSquare
/-- Legendre's three-square theorem: n is a sum of three squares iff n is NOT of the
    form 4^a·(8b+7). -/

def ankeny_Q1 (n q : ℕ) (x y z : ℤ) : ℤ := q * x^2 + y^2 + n * z^2

/-- If
- `q ≡ -1 [ZMOD n]`,
- `x ≡ y [ZMOD n]`,
- `y ≡ b*z [ZMOD q]`, and
- `b^2 ≡ -n [ZMOD q]`,

then `Q₁(x,y,z) ≡ 0 [ZMOD n*q]` (CRT, assuming `gcd(n,q)=1`).

This is the arithmetic interface needed for a future `n % 8 = 5` lattice. -/
