import Mathlib
namespace Brockian.TwoSquaresUnique

/-- If `p` is prime and `p = a^2 + b^2`, then `a > 0`. -/

private lemma brahmagupta_two (a b c d : ℤ) :
    (a ^ 2 + b ^ 2) * (c ^ 2 + d ^ 2) = (a * c - b * d) ^ 2 + (a * d + b * c) ^ 2 := by
  ring

/-- `p` divides the product `(ad - bc)(ad + bc)`. -/
