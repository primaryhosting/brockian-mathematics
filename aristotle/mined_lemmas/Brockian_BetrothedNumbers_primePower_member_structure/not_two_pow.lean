import Mathlib
/-!
# Prime Power Member Structure
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.primePower_member_structure
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators

set_option maxHeartbeats 1000000

namespace Brockian
namespace BetrothedNumbers

open Finset ArithmeticFunction

/-- A pair of *betrothed* (quasi-amicable) numbers: two distinct positive integers each of
whose divisor sums equals the sum of the two numbers plus one. -/

lemma not_two_pow {a n : ℕ} (h : IsBetrothedPair (2 ^ a) n) : False := by
  have hpe := partner_eq Nat.prime_two h
  have ha := two_le_exponent Nat.prime_two h
  have hgeom : ∑ i ∈ Finset.range a, (2 : ℕ) ^ i = 2 ^ a - 1 := by
    simpa using Nat.geomSum_eq (le_refl 2) a
  rw [hgeom] at hpe
  obtain ⟨b, rfl⟩ : ∃ b, a = b + 1 := ⟨a - 1, by omega⟩
  have h2b : 1 ≤ 2 ^ b := Nat.one_le_two_pow
  have hpow : (2 : ℕ) ^ (b + 1) = 2 * 2 ^ b := by ring
  set q : ℕ := 2 ^ b - 1 with hqdef
  have hn : n = 2 * q := by omega
  have hqodd : Odd q := by
    obtain ⟨c, hc⟩ : 2 ∣ 2 ^ b := dvd_pow_self 2 (by omega)
    exact ⟨c - 1, by omega⟩
  have hcop : Nat.Coprime 2 q := Nat.coprime_two_left.mpr hqodd
  have hs2 : ArithmeticFunction.sigma 1 2 = 3 := by decide
  have hsig : ArithmeticFunction.sigma 1 n = 3 * ArithmeticFunction.sigma 1 q := by
    rw [hn, ArithmeticFunction.sigma_one_apply, hcop.sum_divisors_mul,
      ← ArithmeticFunction.sigma_one_apply, ← ArithmeticFunction.sigma_one_apply, hs2]
  have heq := h.2.2.2.2
  rw [hsig] at heq
  have key : 3 * ArithmeticFunction.sigma 1 q = 4 * q + 3 := by omega
  by_cases hble : b ≤ 3
  · interval_cases b <;> simp only [hqdef] at key <;> norm_num at key <;> revert key <;> decide
  · have h16 : (16 : ℕ) ≤ 2 ^ b := by
      calc (16 : ℕ) = 2 ^ 4 := by norm_num
      _ ≤ 2 ^ b := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h9 : 9 < q := by omega
    have h3 : 3 ∣ q := by omega
    have := sigma_one_ge_of_three_dvd h3 h9
    omega

/-- The base of a prime-power member of a betrothed pair is odd. -/
