import Mathlib
import RequestProject.ThabitBalance

/-!
# Bridge to Mathlib's `σ₁`

The target file `ThabitBalance.lean` is import-free (its header comment must be the very first
thing in the file, which precludes an `import` command), so it uses its own elementary
sum-of-divisors function `sigmaOne`.  Here we prove that `sigmaOne` agrees with Mathlib's
`ArithmeticFunction.sigma 1`, and restate the balance identity together with the
deficient/perfect/abundant comparisons in Mathlib's language.
-/

open scoped ArithmeticFunction.sigma

namespace Brockian.BetrothedNumbers.Dynamics


theorem thabit_balance_identity_sigma {k p m : Nat}
    (hshape : m + (p + 2) = 2 ^ k * (p + 2))
    (hsigma : σ 1 m + (p + 1) = 2 ^ (k + 1) * (p + 1)) :
    σ 1 m + 2 ^ (k + 1) = 2 * m + (p + 3) := by
  rw [← sigmaOne_eq_sigma_one] at hsigma ⊢
  exact thabit_balance_identity hshape hsigma

/-- Deficiency comparison in Mathlib's language. -/
