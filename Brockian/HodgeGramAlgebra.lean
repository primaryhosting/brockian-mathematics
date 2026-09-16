import Mathlib

/-!
# The algebra after the Hodge-index sign

The positive-semidefinite quadratic form is an explicit hypothesis. These
lemmas do not formalize Hodge index, construct an arithmetic surface, or
produce positivity for the Riemann zeta function.
-/

namespace Brockian.HodgeGramAlgebra

/-- The two-vector Gram determinant inequality from the supplied sign. -/
theorem gram_minor_nonnegative (a b c : ℝ) (ha : 0 < a)
    (hGramSign : ∀ x y : ℝ, 0 ≤ a * x ^ 2 + 2 * b * x * y + c * y ^ 2) :
    0 ≤ a * c - b ^ 2 := by
  have h := hGramSign b (-a)
  have hm : 0 ≤ a * (a * c - b ^ 2) := by nlinarith [h]
  exact nonneg_of_mul_nonneg_left hm ha

/-- Once the geometric sign and the intersection numbers are supplied,
the squared Weil inequality is elementary real algebra. -/
theorem weil_squared_of_gram_sign (g q N : ℝ) (hg : 0 < g)
    (hHodgeGramSign : ∀ x y : ℝ,
      0 ≤ (2 * g) * x ^ 2 + 2 * (q + 1 - N) * x * y + (2 * g * q) * y ^ 2) :
    (N - q - 1) ^ 2 ≤ 4 * g ^ 2 * q := by
  have h := gram_minor_nonnegative (2 * g) (q + 1 - N) (2 * g * q)
    (by linarith) hHodgeGramSign
  nlinarith

/-- The diagonal must use the Euler characteristic, not a point count over F_1. -/
theorem gram_diagonal (g Q : ℝ) : Q * (2 - 2 * g) - Q - Q = -2 * g * Q := by
  ring

end Brockian.HodgeGramAlgebra
