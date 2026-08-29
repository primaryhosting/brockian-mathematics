import Mathlib

/-!
# Prime Power Member Structure
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.primePower_member_structure
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/


open scoped BigOperators
open scoped Nat
open scoped ArithmeticFunction.sigma
open ArithmeticFunction

namespace Brockian.BetrothedNumbers

/-- `IsBetrothedPair m n` says that `(m, n)` is a betrothed (quasi-amicable) pair:
two distinct positive integers each of whose sum of divisors equals `m + n + 1`,
equivalently, the sum of the nontrivial proper divisors of each equals the other. -/

lemma primePower_member_prime_odd {p a n : ℕ} (hp : p.Prime) (h : IsBetrothedPair (p ^ a) n) :
    Odd p := by
  rcases hp.eq_two_or_odd' with rfl | hodd
  case inr => exact hodd
  exfalso
  obtain ⟨b, hab, hnb⟩ := primePower_partner hp h
  obtain ⟨hm, hn, hne, h1, h2⟩ := h
  set t := σ 1 (2 ^ b) with ht
  have hcop : Nat.Coprime 2 t := coprime_sigma_one_primePow Nat.prime_two b
  have hpow : t + 1 = 2 ^ (b + 1) := sigma_one_two_pow b
  have hpow' : (2 : ℕ) ^ (b + 1) = 2 * 2 ^ b := by ring
  have htodd : t % 2 = 1 := by omega
  have hsig : σ 1 n = 3 * σ 1 t := by
    rw [hnb, sigma_one_prime_mul Nat.prime_two hcop]
  have hpow2 : (2 : ℕ) ^ a = 2 * (t + 1) := by rw [hab, hpow]; ring
  have key : 3 * σ 1 t = 4 * t + 3 := by rw [hsig, hpow2, hnb] at h2; omega
  have h3t : t % 3 = 0 := by omega
  obtain ⟨s, hs⟩ : ∃ s, t = 3 * s := ⟨t / 3, by omega⟩
  have hst : σ 1 t = 4 * s + 1 := by rw [hs] at key ⊢; omega
  have hs0 : 1 ≤ s := by
    rcases Nat.eq_zero_or_pos s with rfl | hpos
    · omega
    · exact hpos
  rcases Nat.lt_or_ge s 5 with hlt | hge
  · interval_cases s
    · have ht3 : t = 3 := by omega
      rw [ht3] at hst; revert hst; decide
    · omega
    · -- `t = 9` would force `2 ^ (b + 1) = 10`
      have h10 : (10 : ℕ) = 2 ^ (b + 1) := by omega
      have h5 : (5 : ℕ) ∣ 2 ^ (b + 1) := ⟨2, by omega⟩
      have := Nat.Prime.dvd_of_dvd_pow (p := 5) (by norm_num) h5
      omega
    · omega
  · rw [hs] at hst
    have := sigma_one_three_mul_ge hge
    omega

/-- The partner of an odd prime power member is even. -/
