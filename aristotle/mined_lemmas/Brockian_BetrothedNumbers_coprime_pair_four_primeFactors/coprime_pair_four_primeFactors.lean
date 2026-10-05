import Mathlib

/-!
# Coprime Pair Four Prime Factors
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.coprime_pair_four_primeFactors
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Nat

set_option maxHeartbeats 1000000

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Brockian
namespace BetrothedNumbers

open ArithmeticFunction Finset

/-- `Betrothed m n` says that `m` and `n` are *betrothed* (quasi-amicable) numbers:
both are positive and each one's sum of divisors equals `m + n + 1`. -/

theorem coprime_pair_four_primeFactors {m n : ℕ} (h : Betrothed m n)
    (hmn : Nat.Coprime m n) : 4 ≤ (m * n).primeFactors.card := by
  obtain ⟨hm, hn, hsm, hsn⟩ := h
  have hN : m * n ≠ 0 := Nat.mul_ne_zero (by omega) (by omega)
  have hmul : (sigma 1) (m * n) = (m + n + 1) * (m + n + 1) := by
    rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hmn, hsm, hsn]
  have habund : 4 * (m * n) < (sigma 1) (m * n) := by
    rw [hmul]
    have hz : (4 : ℤ) * (m * n) < ((m : ℤ) + n + 1) * ((m : ℤ) + n + 1) := by
      have h1 : (1 : ℤ) ≤ (m : ℤ) := by exact_mod_cast hm
      have h2 : (1 : ℤ) ≤ (n : ℤ) := by exact_mod_cast hn
      nlinarith [sq_nonneg ((m : ℤ) - n)]
    exact_mod_cast hz
  exact four_le_card_primeFactors_of_abundancy hN habund

end BetrothedNumbers
end Brockian

