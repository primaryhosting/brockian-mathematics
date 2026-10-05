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


def sigmaOne (m : Nat) : Nat := sigmaAux m m

/-- The Thabit-style shape criterion, written subtraction-free:
`m + (p + 2) = 2 ^ k * (p + 2)`, i.e. `m = (2 ^ k - 1) * (p + 2)`. -/
