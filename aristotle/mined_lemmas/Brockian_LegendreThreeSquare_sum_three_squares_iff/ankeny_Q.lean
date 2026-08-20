import Mathlib
import GeometryOfNumbers.Legendre.Main
namespace Brockian.LegendreThreeSquare
/-- Legendre's three-square theorem: n is a sum of three squares iff n is NOT of the
    form 4^a·(8b+7). -/

def ankeny_Q (n q : ℕ) (x y z : ℤ) : ℤ := 2 * q * x^2 + y^2 + n * z^2

/-!
### A `q ≡ -1 (mod n)` arithmetic glue lemma

For the remaining reduced residue class `n % 8 = 5`, the same *shape* of argument is plausible,
but with a different modulus choice: take `q ≡ -1 (mod n)` and use
\[
  Q_1(x,y,z) = qx^2 + y^2 + nz^2.
\]

This section only extracts the modular-arithmetic glue (no geometry yet).
-/

/-- The quadratic form `Q₁ = qx² + y² + nz²` (integer-valued). -/
