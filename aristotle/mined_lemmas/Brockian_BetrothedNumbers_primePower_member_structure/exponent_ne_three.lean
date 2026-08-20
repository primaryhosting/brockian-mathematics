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

lemma exponent_ne_three {p n : ℕ} (hp : p.Prime) (h : IsBetrothedPair (p ^ 3) n) : False := by
  have hodd : Odd p := base_odd hp h
  have hp2 : p % 2 = 1 := Nat.odd_iff.mp hodd
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    omega
  have hpe := partner_eq hp h
  simp [Finset.sum_range_succ] at hpe
  have hn : n = p * (1 + p) := by nlinarith [hpe]
  have hcop : Nat.Coprime p (1 + p) := by
    simp
  have hsig : ArithmeticFunction.sigma 1 n = (p + 1) * ArithmeticFunction.sigma 1 (1 + p) := by
    rw [hn, ArithmeticFunction.sigma_one_apply, hcop.sum_divisors_mul,
      ← ArithmeticFunction.sigma_one_apply, ← ArithmeticFunction.sigma_one_apply,
      sigma_one_prime hp]
  have heq := h.2.2.2.2
  rw [hsig, hn] at heq
  have hkey : (p + 1) * ArithmeticFunction.sigma 1 (1 + p) = (p + 1) * (p ^ 2 + 1) := by
    rw [heq]; ring
  have hcancel : ArithmeticFunction.sigma 1 (1 + p) = p ^ 2 + 1 :=
    Nat.eq_of_mul_eq_mul_left (by omega) hkey
  have hbound := two_mul_sigma_one_le (1 + p)
  rw [hcancel] at hbound
  have hple : p ≤ 3 := by nlinarith
  have hp3' : p = 3 := by omega
  subst hp3'
  norm_num at hcancel
  revert hcancel
  decide

/-- **Hagis–Lord, Proposition 4.** If a prime power `p ^ a` is a member of a betrothed pair
with partner `n`, then `p` is odd, `a` is odd and larger than `3`, and `n` is even. -/
