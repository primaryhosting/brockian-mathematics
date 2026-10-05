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


theorem sigmaAux_eq_sum (m : Nat) :
    ∀ n : Nat, sigmaAux m n = ∑ d ∈ Finset.range (n + 1), if d ∣ m then d else 0
  | 0 => by simp [sigmaAux]
  | n + 1 => by
      rw [Finset.sum_range_succ, ← sigmaAux_eq_sum m n]
      rfl

