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
def IsBetrothedPair (m n : ℕ) : Prop :=
  0 < m ∧ 0 < n ∧ m ≠ n ∧
    ArithmeticFunction.sigma 1 m = m + n + 1 ∧ ArithmeticFunction.sigma 1 n = m + n + 1

/-- Sanity check: `(48, 75)` is a betrothed pair, so the definition is not vacuous. -/
lemma isBetrothedPair_48_75 : IsBetrothedPair 48 75 := by
  refine ⟨by norm_num, by norm_num, by norm_num, ?_, ?_⟩ <;> decide

/-- Being a betrothed pair is a symmetric relation. -/
lemma IsBetrothedPair.symm {m n : ℕ} (h : IsBetrothedPair m n) : IsBetrothedPair n m := by
  obtain ⟨hm, hn, hne, h1, h2⟩ := h
  refine ⟨hn, hm, hne.symm, ?_, ?_⟩
  · rw [h2]; ring
  · rw [h1]; ring

/-- The divisor sum of `k` is at most `1 + 2 + ⋯ + k`. -/
lemma two_mul_sigma_one_le (k : ℕ) :
    2 * ArithmeticFunction.sigma 1 k ≤ k * (k + 1) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  have hsub : k.divisors ⊆ Finset.range (k + 1) := by
    intro d hd
    rw [Nat.mem_divisors] at hd
    exact Finset.mem_range.2 (Nat.lt_succ_of_le (Nat.le_of_dvd hk hd.1))
  have h1 : ArithmeticFunction.sigma 1 k ≤ ∑ i ∈ Finset.range (k + 1), i := by
    rw [ArithmeticFunction.sigma_one_apply]
    exact Finset.sum_le_sum_of_subset hsub
  have h2 : (∑ i ∈ Finset.range (k + 1), i) * 2 = (k + 1) * k := by
    simpa using Finset.sum_range_id_mul_two (k + 1)
  have h3 : k * (k + 1) = (k + 1) * k := by ring
  omega

/-- If `q > 9` is divisible by `3`, then `1`, `3`, `q / 3` and `q` are four distinct divisors
of `q`; this gives a lower bound for its divisor sum. -/
lemma sigma_one_ge_of_three_dvd {q : ℕ} (h3 : 3 ∣ q) (h9 : 9 < q) :
    q + q / 3 + 4 ≤ ArithmeticFunction.sigma 1 q := by
  obtain ⟨r, rfl⟩ := h3
  have hr : 3 < r := by omega
  have hdiv : 3 * r / 3 = r := by omega
  have hsub : ({1, 3, r, 3 * r} : Finset ℕ) ⊆ (3 * r).divisors := by
    intro d hd
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd
    rw [Nat.mem_divisors]
    refine ⟨?_, by omega⟩
    rcases hd with rfl | rfl | rfl | rfl
    · exact one_dvd _
    · exact ⟨r, rfl⟩
    · exact ⟨3, by ring⟩
    · exact dvd_rfl
  have hsum : ∑ d ∈ ({1, 3, r, 3 * r} : Finset ℕ), d = 1 + 3 + r + 3 * r := by
    rw [Finset.sum_insert (by simp; omega), Finset.sum_insert (by simp; omega),
      Finset.sum_insert (by simp; omega), Finset.sum_singleton]
    ring
  have h2 : 1 + 3 + r + 3 * r ≤ ∑ d ∈ (3 * r).divisors, d := by
    simpa [hsum] using Finset.sum_le_sum_of_subset (f := fun d => d) hsub
  rw [ArithmeticFunction.sigma_one_apply, hdiv]
  omega

/-- The divisor sum of a prime. -/
lemma sigma_one_prime {p : ℕ} (hp : p.Prime) : ArithmeticFunction.sigma 1 p = p + 1 := by
  have h := ArithmeticFunction.sigma_one_apply_prime_pow (p := p) (i := 1) hp
  simp [Finset.sum_range_succ, add_comm] at h
  simpa [add_comm] using h

/-- For odd `p`, the geometric sum `1 + p + ⋯ + p ^ (a - 1)` has the parity of `a`. -/
lemma geomSum_mod_two {p : ℕ} (hp : Odd p) (a : ℕ) :
    (∑ i ∈ Finset.range a, p ^ i) % 2 = a % 2 := by
  induction a with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ]
    have : p ^ k % 2 = 1 := Nat.odd_iff.mp hp.pow
    omega

/-- Partner formula: if `p ^ a` belongs to a betrothed pair with partner `n`, then
`n + 1 = 1 + p + ⋯ + p ^ (a - 1)`. -/
lemma partner_eq {p a n : ℕ} (hp : p.Prime) (h : IsBetrothedPair (p ^ a) n) :
    n + 1 = ∑ i ∈ Finset.range a, p ^ i := by
  have h1 := h.2.2.2.1
  rw [ArithmeticFunction.sigma_one_apply_prime_pow hp, geom_sum_succ'] at h1
  omega

/-- A prime-power member of a betrothed pair has exponent at least `2`. -/
lemma two_le_exponent {p a n : ℕ} (hp : p.Prime) (h : IsBetrothedPair (p ^ a) n) : 2 ≤ a := by
  have hpe := partner_eq hp h
  rcases a with _ | _ | a
  · simp at hpe
  · simp at hpe
    have := h.2.1
    omega
  · omega

/-- No power of two is a member of a betrothed pair. -/
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
lemma base_odd {p a n : ℕ} (hp : p.Prime) (h : IsBetrothedPair (p ^ a) n) : Odd p := by
  rcases hp.eq_two_or_odd' with rfl | hodd
  · exact absurd h not_two_pow
  · exact hodd

/-- The exponent of a prime-power member of a betrothed pair is odd. -/
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
theorem primePower_member_structure {p a n : ℕ} (hp : p.Prime) (h : IsBetrothedPair (p ^ a) n) :
    Odd p ∧ Odd a ∧ 3 < a ∧ Even n := by
  have hodd : Odd p := base_odd hp h
  have hao : Odd a := exponent_odd hp h
  have ha2 : 2 ≤ a := two_le_exponent hp h
  have ha3 : a ≠ 3 := by
    rintro rfl
    exact exponent_ne_three hp h
  have hgt : 3 < a := by
    rcases hao with ⟨k, hk⟩
    omega
  refine ⟨hodd, hao, hgt, ?_⟩
  have hpe := partner_eq hp h
  have h1 := geomSum_mod_two hodd a
  have h2 : a % 2 = 1 := Nat.odd_iff.mp hao
  exact Nat.even_iff.mpr (by omega)

/-- Both members of a betrothed pair cannot be prime powers. -/
theorem not_both_primePower {p a q b : ℕ} (hp : p.Prime) (hq : q.Prime)
    (h : IsBetrothedPair (p ^ a) (q ^ b)) : False := by
  obtain ⟨hpodd, -, -, -⟩ := primePower_member_structure hp h
  obtain ⟨-, -, -, hevenp⟩ := primePower_member_structure hq h.symm
  exact (Nat.not_odd_iff_even.mpr hevenp) hpodd.pow

end BetrothedNumbers
end Brockian

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

