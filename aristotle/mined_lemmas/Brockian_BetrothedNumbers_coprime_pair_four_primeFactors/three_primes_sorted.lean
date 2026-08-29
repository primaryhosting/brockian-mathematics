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

lemma three_primes_sorted {a b c : ℕ} (ha : a.Prime) (hb : b.Prime) (hc : c.Prime)
    (hab : a < b) (hbc : b < c) :
    a * b * c ≤ 4 * ((a - 1) * (b - 1) * (c - 1)) := by
  have ha2 : 2 ≤ a := ha.two_le
  have hb3 : 3 ≤ b := by omega
  have hc5 : 5 ≤ c := by
    have h4 : c ≠ 4 := by rintro rfl; norm_num at hc
    omega
  obtain ⟨A, rfl⟩ : ∃ A, a = A + 1 := ⟨a - 1, by omega⟩
  obtain ⟨B, rfl⟩ : ∃ B, b = B + 1 := ⟨b - 1, by omega⟩
  obtain ⟨C, rfl⟩ : ∃ C, c = C + 1 := ⟨c - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  exact succ_prod_le_four_mul A B C (by omega) (by omega) (by omega)

/-- Three distinct primes: `a * b * c ≤ 4 * ((a-1) * (b-1) * (c-1))`. -/
