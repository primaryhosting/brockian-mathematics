import Mathlib
import RequestProject.ThabitBalanceIdentity

/-!
# Thabit Balance Identity — Mathlib interface

This file connects the self-contained divisor-sum `sigmaOne` used in
`RequestProject.ThabitBalanceIdentity` with Mathlib's `ArithmeticFunction.sigma 1`, and restates
the Thabit balance identity and the deficient/perfect/abundant comparisons in Mathlib terms.
-/

namespace Brockian.BetrothedNumbers.Dynamics

open ArithmeticFunction

/-- `sigmaOne` is Mathlib's sum-of-divisors function `σ₁`. -/

theorem thabit_shape_add {k p m : Nat} (hm : m = (2 ^ k - 1) * (p + 2)) :
    m + (p + 2) = 2 ^ k * p + 2 * 2 ^ k := by
  have hA : 0 < 2 ^ k := Nat.two_pow_pos k
  obtain ⟨a, ha⟩ : ∃ a, 2 ^ k = a + 1 := ⟨2 ^ k - 1, by omega⟩
  rw [hm, ha]
  simp [Nat.succ_mul, Nat.mul_add]
  omega

/-- **Thabit balance identity.** Under the Thabit sigma criterion, the subtraction-free
balance identity `σ(m) + 2 ^ (k + 1) = 2 * m + (p + 3)` holds. -/
