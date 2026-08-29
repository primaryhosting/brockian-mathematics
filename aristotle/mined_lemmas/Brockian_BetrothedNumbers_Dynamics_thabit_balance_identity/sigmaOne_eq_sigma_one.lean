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


theorem sigmaOne_eq_sigma_one (m : Nat) : sigmaOne m = σ 1 m := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp [sigmaOne, sigmaAux]
  · rw [sigmaOne, sigmaAux_eq_sum, ArithmeticFunction.sigma_one_apply,
      divisors_eq_filter_range (Nat.ne_of_gt hm).symm, Finset.sum_filter]

/-- **Thabit balance identity**, stated with Mathlib's `σ₁`. -/
