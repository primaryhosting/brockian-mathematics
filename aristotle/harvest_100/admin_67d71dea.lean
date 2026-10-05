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

import Mathlib

/-!
# Quasiperfect Exists
Category: Brockian Conjecture
Target: Brockian.QuasiperfectNumbers.QuasiperfectExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.QuasiperfectNumbers

open Finset

/-- A natural number `n` is *quasiperfect* if the sum of its divisors equals `2 * n + 1`,
i.e. the sum of its proper divisors is `n + 1`. -/
def Quasiperfect (n : ℕ) : Prop := ArithmeticFunction.sigma 1 n = 2 * n + 1

lemma sigma_one_eq_sum_divisors (n : ℕ) :
    ArithmeticFunction.sigma 1 n = ∑ d ∈ n.divisors, d := by
  simp [ArithmeticFunction.sigma_apply]

/-- A number congruent to `3` mod `4` has a prime factor congruent to `3` mod `4`. -/
lemma exists_prime_factor_three_mod_four :
    ∀ n : ℕ, n % 4 = 3 → ∃ p : ℕ, p.Prime ∧ p ∣ n ∧ p % 4 = 3 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    have hn1 : n ≠ 1 := by omega
    set p := n.minFac with hp
    have hpp : p.Prime := Nat.minFac_prime hn1
    obtain ⟨q, hq⟩ : p ∣ n := Nat.minFac_dvd n
    have hpodd : p % 2 = 1 := by
      rcases hpp.eq_two_or_odd with h2 | h2
      · exfalso; rw [h2] at hq; omega
      · exact h2
    rcases (by omega : p % 4 = 1 ∨ p % 4 = 3) with h1 | h3
    · have hq4 : q % 4 = 3 := by
        have hnq : n % 4 = q % 4 := by
          rw [hq, Nat.mul_mod, h1, one_mul, Nat.mod_mod]
        omega
      have hqlt : q < n := by
        have hp3 : 3 ≤ p := by have := hpp.two_le; omega
        have hq3 : 3 ≤ q := by omega
        calc q < 3 * q := by omega
          _ ≤ p * q := Nat.mul_le_mul_right q hp3
          _ = n := hq.symm
      obtain ⟨r, hr, hrd, hr4⟩ := ih q hqlt hq4
      exact ⟨r, hr, hrd.trans ⟨p, by rw [hq]; ring⟩, hr4⟩
    · exact ⟨p, hpp, Nat.minFac_dvd n, h3⟩

/-- If `p` is a prime congruent to `3` mod `4`, then `p` does not divide `t ^ 2 + 1`. -/
lemma not_dvd_sq_add_one {p t : ℕ} (hp : p.Prime) (hp4 : p % 4 = 3) : ¬ p ∣ t ^ 2 + 1 := by
  intro hdvd
  haveI : Fact p.Prime := ⟨hp⟩
  have h0 : ((t ^ 2 + 1 : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ p).mpr hdvd
  push_cast at h0
  have hsq : IsSquare (-1 : ZMod p) := ⟨(t : ZMod p), by linear_combination -h0⟩
  exact (ZMod.exists_sq_eq_neg_one_iff.mp hsq) hp4

/-- If `n` has an odd number of divisors, then `n` is a perfect square. -/
lemma isSquare_of_odd_card_divisors {n : ℕ} (hn : n ≠ 0) (h : Odd n.divisors.card) :
    IsSquare n := by
  rw [Nat.card_divisors hn] at h
  have heven : ∀ p ∈ n.primeFactors, Even (n.factorization p) := by
    intro p hp
    have hdvd : (n.factorization p + 1) ∣ ∏ x ∈ n.primeFactors, (n.factorization x + 1) :=
      Finset.dvd_prod_of_mem _ hp
    rcases Nat.even_or_odd (n.factorization p) with he | ho
    · exact he
    · exfalso
      rw [Nat.odd_iff] at h ho
      have h2 : 2 ∣ ∏ x ∈ n.primeFactors, (n.factorization x + 1) :=
        dvd_trans (by omega) hdvd
      omega
  have key : ∏ p ∈ n.primeFactors, p ^ n.factorization p = n := by
    conv_rhs => rw [← Nat.factorization_prod_pow_eq_self hn]
    rw [Finsupp.prod, Nat.support_factorization]
  refine ⟨∏ p ∈ n.primeFactors, p ^ (n.factorization p / 2), ?_⟩
  rw [← Finset.prod_mul_distrib]
  have hcongr : ∀ p ∈ n.primeFactors, p ^ (n.factorization p / 2) * p ^ (n.factorization p / 2)
      = p ^ (n.factorization p) := by
    intro p hp
    rw [← pow_add]
    congr 1
    obtain ⟨k, hk⟩ := heven p hp
    omega
  rw [Finset.prod_congr rfl hcongr, key]

/-- For odd `n`, the sum of divisors has the same parity as the number of divisors. -/
lemma sigma_mod_two_of_odd {n : ℕ} (hn : Odd n) :
    ArithmeticFunction.sigma 1 n % 2 = n.divisors.card % 2 := by
  have hall : ∀ d ∈ n.divisors, d % 2 = 1 := fun d hd =>
    Nat.odd_iff.mp (hn.of_dvd_nat (Nat.mem_divisors.mp hd).1)
  rw [sigma_one_eq_sum_divisors, Finset.sum_nat_mod, Finset.sum_congr rfl hall]
  simp

/-- An odd number with an odd sum of divisors is a perfect square. -/
lemma isSquare_of_odd_of_odd_sigma {n : ℕ} (hn0 : n ≠ 0) (hn : Odd n)
    (hs : Odd (ArithmeticFunction.sigma 1 n)) : IsSquare n := by
  refine isSquare_of_odd_card_divisors hn0 (Nat.odd_iff.mpr ?_)
  rw [← sigma_mod_two_of_odd hn, Nat.odd_iff.mp hs]

private lemma sum_two_pow_range (k : ℕ) :
    (∑ i ∈ Finset.range (k + 1), 2 ^ i) + 1 = 2 ^ (k + 1) := by
  induction k with
  | zero => decide
  | succ j ih =>
    rw [Finset.sum_range_succ]
    ring_nf
    ring_nf at ih
    omega

/-- The sum of divisors of `2 ^ k`. -/
lemma sigma_two_pow (k : ℕ) :
    ArithmeticFunction.sigma 1 (2 ^ k) + 1 = 2 ^ (k + 1) := by
  have h : ArithmeticFunction.sigma 1 (2 ^ k) = ∑ i ∈ Finset.range (k + 1), 2 ^ i := by
    simp only [ArithmeticFunction.sigma_apply, pow_one]
    exact Nat.sum_divisors_prime_pow Nat.prime_two
  rw [h, sum_two_pow_range]

/-- **Cattaneo-type parity result**: a quasiperfect number is odd. -/
theorem quasiperfect_odd {n : ℕ} (hn : 0 < n) (h : Quasiperfect n) : Odd n := by
  rcases Nat.even_or_odd n with he | ho
  swap
  · exact ho
  exfalso
  obtain ⟨k, m, hm, hnm⟩ := Nat.exists_eq_two_pow_mul_odd hn.ne'
  have hk1 : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with hk | hk
    · exfalso
      rw [hk, pow_zero, one_mul] at hnm
      rw [hnm] at he
      exact (Nat.not_odd_iff_even.mpr he) hm
    · exact hk
  have hcop : Nat.Coprime (2 ^ k) m :=
    Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hm)
  have hmul : ArithmeticFunction.sigma 1 n
      = ArithmeticFunction.sigma 1 (2 ^ k) * ArithmeticFunction.sigma 1 m := by
    rw [hnm]
    exact ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop
  set d := ArithmeticFunction.sigma 1 (2 ^ k) with hd
  have hd1 : d + 1 = 2 ^ (k + 1) := sigma_two_pow k
  have heq : d * ArithmeticFunction.sigma 1 m = 2 * (2 ^ k * m) + 1 := by
    rw [← hmul, h, hnm]
  have e1 : 2 * (2 ^ k * m) = (d + 1) * m := by rw [hd1]; ring
  rw [e1] at heq
  have hdm : d * ArithmeticFunction.sigma 1 m = d * m + (m + 1) := by rw [heq]; ring
  have hdvd : d ∣ m + 1 := by
    have h3 : d ∣ d * ArithmeticFunction.sigma 1 m - d * m := Nat.dvd_sub ⟨_, rfl⟩ ⟨_, rfl⟩
    have h4 : d * ArithmeticFunction.sigma 1 m - d * m = m + 1 := by omega
    rwa [h4] at h3
  have hsodd : Odd (ArithmeticFunction.sigma 1 m) := by
    have hodd_total : Odd (ArithmeticFunction.sigma 1 n) := by rw [h]; exact ⟨n, by ring⟩
    rw [hmul] at hodd_total
    exact (Nat.odd_mul.mp hodd_total).2
  have hm0 : m ≠ 0 := by
    rintro rfl
    simp at hm
  obtain ⟨t, ht⟩ := isSquare_of_odd_of_odd_sigma hm0 hm hsodd
  have hd4 : d % 4 = 3 := by
    have h4 : (4 : ℕ) ∣ 2 ^ (k + 1) := by
      refine ⟨2 ^ (k - 1), ?_⟩
      rw [show k + 1 = 2 + (k - 1) by omega, pow_add]
      norm_num
    omega
  obtain ⟨q, hq, hqd, hq4⟩ := exists_prime_factor_three_mod_four d hd4
  have hqm : q ∣ t ^ 2 + 1 := by
    have hqm' : q ∣ m + 1 := hqd.trans hdvd
    rwa [ht, ← pow_two] at hqm'
  exact not_dvd_sq_add_one hq hq4 hqm

/-- A quasiperfect number is a perfect square. -/
theorem quasiperfect_isSquare {n : ℕ} (hn : 0 < n) (h : Quasiperfect n) : IsSquare n := by
  refine isSquare_of_odd_of_odd_sigma hn.ne' (quasiperfect_odd hn h) ?_
  rw [h]
  exact ⟨n, by ring⟩

/-- **Reduction of the existence question for quasiperfect numbers.**

A quasiperfect number exists if and only if there is an odd number `m > 1` whose square is
quasiperfect.  (Whether such a number exists is an open problem; this is a Lean-checked
equivalent reformulation, which in particular shows that any quasiperfect number is
necessarily the square of an odd number greater than `1`.) -/
theorem QuasiperfectExists :
    (∃ n : ℕ, 0 < n ∧ Quasiperfect n) ↔ (∃ m : ℕ, Odd m ∧ 1 < m ∧ Quasiperfect (m ^ 2)) := by
  constructor
  · rintro ⟨n, hn, h⟩
    obtain ⟨m, hm⟩ := quasiperfect_isSquare hn h
    have hn2 : n = m ^ 2 := by rw [hm]; ring
    have hmodd : Odd m := by
      have hnodd : Odd n := quasiperfect_odd hn h
      rcases Nat.even_or_odd m with he | ho
      · exfalso
        rw [Nat.even_iff] at he
        rw [hn2, Nat.odd_iff, Nat.pow_mod, he] at hnodd
        simp at hnodd
      · exact ho
    have hm1 : 1 < m := by
      rcases Nat.lt_or_ge m 2 with hlt | hge
      · exfalso
        interval_cases m
        · simp at hn2
          omega
        · rw [hn2, Quasiperfect] at h
          norm_num [ArithmeticFunction.isMultiplicative_sigma.map_one] at h
      · omega
    exact ⟨m, hmodd, hm1, hn2 ▸ h⟩
  · rintro ⟨m, _, hm1, h⟩
    exact ⟨m ^ 2, pow_pos (by omega) 2, h⟩

end Brockian.QuasiperfectNumbers

