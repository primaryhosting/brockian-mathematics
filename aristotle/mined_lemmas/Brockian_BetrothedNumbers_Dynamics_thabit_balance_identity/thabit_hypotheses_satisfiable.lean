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


theorem thabit_hypotheses_satisfiable : ThabitShape 1 0 2 ∧ SigmaCriterion 1 0 2 := by
  constructor
  · show 2 + (0 + 2) = 2 ^ 1 * (0 + 2)
    decide
  · show sigmaOne 2 + (0 + 1) = 2 ^ (1 + 1) * (0 + 1)
    decide

/-- Deficiency comparison: `m` is deficient iff `p + 3 < 2 ^ (k + 1)`. -/
