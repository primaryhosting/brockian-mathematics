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

lemma exponent_odd {p a n : ℕ} (hp : p.Prime) (h : IsBetrothedPair (p ^ a) n) : Odd a := by
  have hodd : Odd p := base_odd hp h
  have hpe := partner_eq hp h
  have ha := two_le_exponent hp h
  rcases Nat.even_or_odd a with hae | hao
  swap
  · exact hao
  exfalso
  have hnodd : n % 2 = 1 := by
    have h1 := geomSum_mod_two hodd a
    have h2 : a % 2 = 0 := Nat.even_iff.mp hae
    omega
  obtain ⟨c, rfl⟩ : ∃ c, a = c + 1 := ⟨a - 1, by omega⟩
  have hgs : ∑ i ∈ Finset.range (c + 1), p ^ i = p * (∑ i ∈ Finset.range c, p ^ i) + 1 :=
    geom_sum_succ
  set t : ℕ := ∑ i ∈ Finset.range c, p ^ i with ht
  have hn : n = p * t := by omega
  obtain ⟨d, hd⟩ : ∃ d, t = 1 + p * d := by
    obtain ⟨e, rfl⟩ : ∃ e, c = e + 1 := ⟨c - 1, by omega⟩
    exact ⟨∑ i ∈ Finset.range e, p ^ i, by rw [ht]; simpa [add_comm] using geom_sum_succ⟩
  have hcop : Nat.Coprime p t := by
    rw [hd]
    simp
  have hsig : ArithmeticFunction.sigma 1 n = (p + 1) * ArithmeticFunction.sigma 1 t := by
    rw [hn, ArithmeticFunction.sigma_one_apply, hcop.sum_divisors_mul,
      ← ArithmeticFunction.sigma_one_apply, ← ArithmeticFunction.sigma_one_apply,
      sigma_one_prime hp]
  have heq := h.2.2.2.2
  rw [hsig] at heq
  have hpa : p ^ (c + 1) % 2 = 1 := Nat.odd_iff.mp hodd.pow
  have hp2 : p % 2 = 1 := Nat.odd_iff.mp hodd
  have hmod : ((p + 1) * ArithmeticFunction.sigma 1 t) % 2 = 0 := by
    have h0 : (p + 1) % 2 = 0 := by omega
    rw [Nat.mul_mod, h0]
    simp
  omega

/-- The exponent of a prime-power member of a betrothed pair is not `3`. -/
