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


def sigmaAux (m : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => sigmaAux m n + (if n + 1 ∣ m then n + 1 else 0)

/-- The sum-of-divisors function `σ₁`.  It agrees with Mathlib's `Nat.sigma 1`; see
`Brockian.BetrothedNumbers.Dynamics.sigmaOne_eq_sigma_one` in `ThabitBalanceMathlib.lean`. -/
