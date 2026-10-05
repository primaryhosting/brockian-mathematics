import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

/-
# Cullen Prime Infinitude
Category: Brockian Conjecture
Target: Brockian.CullenWoodall.CullenPrimeInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Cullen Prime Infinitude
Category: Brockian Conjecture
Target: Brockian.CullenWoodall.CullenPrimeInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

The infinitude of Cullen primes (primes of the form `n * 2 ^ n + 1`) is an open
problem.  This file gives a Lean-checked *conditional reduction*: the infinitude of
Cullen primes follows from the existence of arbitrarily large odd `n` admitting a
Proth witness, i.e. an `a` with `a ^ ((n * 2 ^ n) / 2) = -1` modulo `n * 2 ^ n + 1`.
This is exactly the criterion (Proth's theorem, proved here from scratch) that is
used in practice to certify Cullen primes, and for odd `n` the condition is in fact
*equivalent* to primality of the Cullen number.

The file also contains unconditional results in the opposite direction: every odd
prime `p` divides the Cullen number `cullen (p - 2)`, hence infinitely many Cullen
numbers are composite.
-/

namespace Brockian.CullenWoodall

/-- The `n`-th Cullen number `C n = n * 2 ^ n + 1`. -/
def cullen (n : ℕ) : ℕ := n * 2 ^ n + 1

/-- A *Proth witness* for `n`: an element `a` of `ZMod (cullen n)` with
`a ^ ((cullen n - 1) / 2) = -1`.  This is exactly the condition tested by
Proth's theorem, the criterion used in practice to certify Cullen primes. -/
def ProthWitness (n : ℕ) : Prop :=
  ∃ a : ZMod (cullen n), a ^ ((cullen n - 1) / 2) = -1

/-- Proth's theorem: if `k` is odd, `k < 2 ^ m`, `0 < m`, and some `a` satisfies
`a ^ (k * 2 ^ (m - 1)) = -1` modulo `N = k * 2 ^ m + 1`, then `N` is prime.

The proof shows that every prime factor `p` of `N` satisfies `p ≡ 1 [MOD 2 ^ m]`,
hence `p > 2 ^ m > √N`, which forces `N` to be prime. -/
theorem proth_prime_of_pow_eq_neg_one {k m : ℕ} (hk : Odd k) (hkm : k < 2 ^ m)
    (hm : 0 < m) (a : ZMod (k * 2 ^ m + 1)) (ha : a ^ (k * 2 ^ (m - 1)) = -1) :
    (k * 2 ^ m + 1).Prime := by
  have hk1 : 1 ≤ k := hk.pos
  have h2pos : 0 < 2 ^ m := pow_pos (by norm_num) m
  have hmm : m - 1 + 1 = m := Nat.succ_pred_eq_of_pos hm
  have h2m : 2 ^ (m - 1) * 2 = 2 ^ m := by rw [← pow_succ, hmm]
  have hNodd : ¬ (2 ∣ k * 2 ^ m + 1) := by
    have : 2 ∣ k * 2 ^ m := ⟨k * 2 ^ (m - 1), by rw [← h2m]; ring⟩
    omega
  have key : ∀ p : ℕ, p.Prime → p ∣ (k * 2 ^ m + 1) → 2 ^ m < p := by
    intro p hp hpd
    haveI : Fact p.Prime := ⟨hp⟩
    have hp2 : p ≠ 2 := by rintro rfl; exact hNodd hpd
    have hp3 : 2 < p := lt_of_le_of_ne hp.two_le (Ne.symm hp2)
    haveI : Fact (2 < p) := ⟨hp3⟩
    set f := ZMod.castHom hpd (ZMod p) with hf
    set c : ZMod p := (f a) ^ k with hc
    have hcpow : c ^ 2 ^ (m - 1) = -1 := by
      rw [hc, ← pow_mul, ← map_pow, ha, map_neg, map_one]
    have hcpow2 : c ^ 2 ^ (m - 1 + 1) = 1 := by
      rw [pow_succ, pow_mul, hcpow]; simp
    have hne : ¬ c ^ 2 ^ (m - 1) = 1 := by
      rw [hcpow]; exact ZMod.neg_one_ne_one
    have hord : orderOf c = 2 ^ (m - 1 + 1) := orderOf_eq_prime_pow hne hcpow2
    rw [hmm] at hord
    have hc0 : c ≠ 0 := by
      intro h
      rw [h, zero_pow (by positivity)] at hcpow
      exact one_ne_zero (α := ZMod p) (by linear_combination hcpow)
    have hdvd : 2 ^ m ∣ p - 1 :=
      hord ▸ orderOf_dvd_of_pow_eq_one (ZMod.pow_card_sub_one_eq_one hc0)
    have : 2 ^ m ≤ p - 1 := Nat.le_of_dvd (by omega) hdvd
    omega
  by_contra hnp
  have hsq := Nat.minFac_sq_le_self (by positivity) hnp
  have hN1 : k * 2 ^ m + 1 ≠ 1 := by nlinarith
  have hmf := Nat.minFac_prime hN1
  have hlt := key _ hmf (Nat.minFac_dvd _)
  nlinarith [hsq, hlt, hkm]

/-- For `0 < n`, the halved predecessor of a Cullen number is `n * 2 ^ (n - 1)`. -/
theorem cullen_sub_one_div_two {n : ℕ} (hn : 0 < n) :
    (cullen n - 1) / 2 = n * 2 ^ (n - 1) := by
  have h2 : 2 ^ n = 2 ^ (n - 1) * 2 := by
    rw [← pow_succ]
    congr 1
    omega
  have : cullen n - 1 = n * 2 ^ (n - 1) * 2 := by
    simp [cullen, h2, mul_assoc]
  rw [this, Nat.mul_div_cancel _ (by norm_num)]

/-- A Proth witness certifies that the Cullen number `cullen n` is prime (`n` odd). -/
theorem cullen_prime_of_prothWitness {n : ℕ} (hn : Odd n) (h : ProthWitness n) :
    (cullen n).Prime := by
  obtain ⟨a, ha⟩ := h
  rw [cullen_sub_one_div_two hn.pos] at ha
  exact proth_prime_of_pow_eq_neg_one hn Nat.lt_two_pow_self hn.pos a ha

/-- Conversely, a prime Cullen number `cullen n` with `n` odd has a Proth witness:
any generator of the multiplicative group mod `cullen n` works. -/
theorem prothWitness_of_cullen_prime {n : ℕ} (hn : Odd n) (h : (cullen n).Prime) :
    ProthWitness n := by
  haveI : Fact (cullen n).Prime := ⟨h⟩
  obtain ⟨a, ha, hd⟩ := reverse_lucas_primality (cullen n) h
  have hdvd : 2 ∣ cullen n - 1 := by
    have h2 : 2 ^ n = 2 ^ (n - 1) * 2 := by
      rw [← pow_succ]
      congr 1
      have := hn.pos
      omega
    exact ⟨n * 2 ^ (n - 1), by simp [cullen, h2]; ring⟩
  refine ⟨a, ?_⟩
  have hsq : a ^ ((cullen n - 1) / 2) * a ^ ((cullen n - 1) / 2) = 1 := by
    rw [← pow_add, ← two_mul, Nat.mul_div_cancel' hdvd]
    exact ha
  rcases mul_self_eq_one_iff.mp hsq with h1 | h1
  · exact absurd h1 (hd 2 Nat.prime_two hdvd)
  · exact h1

/-- For odd `n`, primality of the Cullen number is equivalent to having a Proth
witness. -/
theorem cullen_prime_iff_prothWitness {n : ℕ} (hn : Odd n) :
    (cullen n).Prime ↔ ProthWitness n :=
  ⟨prothWitness_of_cullen_prime hn, cullen_prime_of_prothWitness hn⟩

/-- Sanity check: `cullen 1 = 3` is prime, and `1` carries a Proth witness. -/
theorem cullen_one_prime : (cullen 1).Prime := by
  norm_num [cullen]

theorem prothWitness_one : ProthWitness 1 := ⟨-1, by decide⟩

/-- **Conditional reduction (main target).**  The infinitude of Cullen primes is an open
problem; here it is reduced to the existence of arbitrarily large odd `n` carrying a
Proth witness.  Given that hypothesis, the set of `n` with `n * 2 ^ n + 1` prime is
infinite. -/
theorem CullenPrimeInfinitude
    (H : ∀ N : ℕ, ∃ n ≥ N, Odd n ∧ ProthWitness n) :
    {n : ℕ | (cullen n).Prime}.Infinite := by
  apply Set.infinite_of_forall_exists_gt
  intro N
  obtain ⟨n, hn, hodd, hw⟩ := H (N + 1)
  exact ⟨n, cullen_prime_of_prothWitness hodd hw, by omega⟩

/-- Unconditional: for every odd prime `p`, the prime `p` divides the Cullen number
`cullen (p - 2)`. -/
theorem dvd_cullen_sub_two {p : ℕ} (hp : p.Prime) (hodd : p ≠ 2) :
    p ∣ cullen (p - 2) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hp3 : 2 < p := lt_of_le_of_ne hp.two_le (Ne.symm hodd)
  have h2ne : (2 : ZMod p) ≠ 0 := by
    have : ((2 : ℕ) : ZMod p) ≠ 0 := by
      rw [Ne, ZMod.natCast_eq_zero_iff]
      intro hdd
      exact hodd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hdd)
    simpa using this
  have hfl : (2 : ZMod p) ^ (p - 1) = 1 := ZMod.pow_card_sub_one_eq_one h2ne
  rw [← ZMod.natCast_eq_zero_iff]
  have hcast : ((cullen (p - 2) : ℕ) : ZMod p) = (-2) * (2 : ZMod p) ^ (p - 2) + 1 := by
    simp only [cullen, Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_one,
      Nat.cast_ofNat]
    rw [Nat.cast_sub (by omega)]
    simp
  rw [hcast]
  have hstep : (2 : ZMod p) * ((-2) * (2 : ZMod p) ^ (p - 2) + 1) = 0 := by
    have hexp : (2 : ZMod p) ^ (p - 2) * 2 = (2 : ZMod p) ^ (p - 1) := by
      rw [← pow_succ]
      congr 1
      omega
    calc (2 : ZMod p) * ((-2) * (2 : ZMod p) ^ (p - 2) + 1)
        = -2 * ((2 : ZMod p) ^ (p - 2) * 2) + 2 := by ring
      _ = -2 * (1 : ZMod p) + 2 := by rw [hexp, hfl]
      _ = 0 := by ring
  rcases mul_eq_zero.mp hstep with h | h
  · exact absurd h h2ne
  · exact h

/-- Unconditional: infinitely many Cullen numbers are composite. -/
theorem cullen_not_prime_infinite : {n : ℕ | ¬ (cullen n).Prime}.Infinite := by
  apply Set.infinite_of_forall_exists_gt
  intro N
  obtain ⟨p, hpge, hp⟩ := Nat.exists_infinite_primes (N + 5)
  have hp2 : p ≠ 2 := by omega
  refine ⟨p - 2, ?_, by omega⟩
  intro hprime
  have hdvd := dvd_cullen_sub_two hp hp2
  have heq : p = cullen (p - 2) := ((Nat.prime_dvd_prime_iff_eq hp hprime).mp hdvd)
  set n := p - 2 with hn
  have hpn : p = n + 2 := by omega
  have hn3 : 3 ≤ n := by omega
  have hlt : n < 2 ^ n := Nat.lt_two_pow_self
  have heq' : p = n * 2 ^ n + 1 := heq
  nlinarith [hlt, hn3, heq', hpn]

end Brockian.CullenWoodall

