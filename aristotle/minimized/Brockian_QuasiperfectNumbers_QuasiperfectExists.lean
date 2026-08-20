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
# Quasiperfect Exists
Category: Brockian Conjecture
Target: Brockian.QuasiperfectNumbers.QuasiperfectExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Quasiperfect numbers

A natural number `n` is *quasiperfect* if `σ(n) = 2n + 1`, i.e. the sum of its proper divisors
is `n + 1`. Whether a quasiperfect number exists is a well-known open problem; none is known.

This file records a **conditional reduction**: the existence of a quasiperfect number is
equivalent to the existence of one satisfying several necessary structural conditions
(`Brockian.QuasiperfectNumbers.QuasiperfectExists`). Along the way we prove, unconditionally:

* no prime power is quasiperfect (`not_quasiperfect_prime_pow`);
* every quasiperfect number is of the form `2 ^ a * m ^ 2` (`Quasiperfect.eq_two_pow_mul_sq`),
  since `σ(n) = 2n + 1` is odd;
* in particular an odd quasiperfect number is a perfect square (`Quasiperfect.isSquare_of_odd`);
* no quasiperfect number is squarefree (`Quasiperfect.not_squarefree`), and no quasiperfect
  number is perfect (`Quasiperfect.not_perfect`);
* there is no quasiperfect number below `101` (`not_quasiperfect_of_lt_101`).
-/

namespace Brockian.QuasiperfectNumbers

open Finset

/-- A natural number `n` is *quasiperfect* if it is positive and the sum of its divisors
equals `2 * n + 1` (equivalently, the sum of its proper divisors is `n + 1`).
No quasiperfect number is known; their existence is an open problem. -/
def Quasiperfect (n : ℕ) : Prop :=
  0 < n ∧ (ArithmeticFunction.sigma 1) n = 2 * n + 1

instance : DecidablePred Quasiperfect := fun n => by unfold Quasiperfect; infer_instance

lemma sigma_one_eq_sum (n : ℕ) : (ArithmeticFunction.sigma 1) n = ∑ d ∈ n.divisors, d := by
  simp [ArithmeticFunction.sigma_one_apply]

/-- No prime power is quasiperfect: for a prime `p`, `σ(p ^ k) < 2 * p ^ k + 1`. -/
lemma not_quasiperfect_prime_pow {p k : ℕ} (hp : p.Prime) : ¬ Quasiperfect (p ^ k) := by
  rintro ⟨-, h⟩
  rw [sigma_one_eq_sum, Nat.sum_divisors_prime_pow hp] at h
  have hZ : (∑ i ∈ range (k + 1), (p : ℤ) ^ i) = 2 * (p : ℤ) ^ k + 1 := by exact_mod_cast h
  have hgeom : (∑ i ∈ range (k + 1), (p : ℤ) ^ i) * ((p : ℤ) - 1) = (p : ℤ) ^ (k + 1) - 1 :=
    geom_sum_mul _ _
  rw [hZ, show (p : ℤ) ^ (k + 1) = (p : ℤ) * (p : ℤ) ^ k from by ring] at hgeom
  have hp2 : (2 : ℤ) ≤ (p : ℤ) := by exact_mod_cast hp.two_le
  have hq1 : (1 : ℤ) ≤ (p : ℤ) ^ k := one_le_pow₀ (by linarith)
  nlinarith [hgeom, hq1, hp2]

/-- No quasiperfect number is a prime power (in particular no prime and no prime square). -/
lemma Quasiperfect.not_isPrimePow {n : ℕ} (h : Quasiperfect n) : ¬ IsPrimePow n := by
  rw [isPrimePow_nat_iff]
  rintro ⟨p, k, hp, -, rfl⟩
  exact not_quasiperfect_prime_pow hp h

/-- For odd `n`, the sum of the divisors of `n` has the same parity as the number of divisors. -/
lemma sum_divisors_mod_two_eq {n : ℕ} (hn : Odd n) :
    (∑ d ∈ n.divisors, d) % 2 = (#n.divisors) % 2 := by
  rw [Finset.sum_nat_mod]
  congr 1
  rw [Finset.sum_congr rfl (fun d hd => ?_), Finset.sum_const, smul_eq_mul, mul_one]
  exact Nat.odd_iff.mp (hn.of_dvd_nat (Nat.mem_divisors.mp hd).1)

/-- A positive natural number with an odd number of divisors is a perfect square. -/
lemma isSquare_of_odd_card_divisors {n : ℕ} (hn : n ≠ 0) (h : Odd (#n.divisors)) :
    IsSquare n := by
  rw [Nat.card_divisors hn] at h
  have heven : ∀ p ∈ n.primeFactors, 2 ∣ n.factorization p := by
    intro p hp
    by_contra hodd
    have h2 : 2 ∣ (n.factorization p + 1) := by omega
    have : 2 ∣ ∏ x ∈ n.primeFactors, (n.factorization x + 1) :=
      h2.trans (Finset.dvd_prod_of_mem _ hp)
    rw [Nat.odd_iff] at h
    omega
  refine ⟨∏ p ∈ n.primeFactors, p ^ (n.factorization p / 2), ?_⟩
  rw [← Finset.prod_mul_distrib]
  conv_lhs => rw [← Nat.factorization_prod_pow_eq_self hn]
  rw [Nat.prod_factorization_eq_prod_primeFactors]
  refine Finset.prod_congr rfl fun p hp => ?_
  rw [← pow_add]
  have := heven p hp
  congr 1
  omega

/-- An odd number with an odd sum of divisors is a perfect square. -/
lemma isSquare_of_odd_of_odd_sigma {m : ℕ} (hm : m ≠ 0) (hodd : Odd m)
    (h : Odd ((ArithmeticFunction.sigma 1) m)) : IsSquare m := by
  refine isSquare_of_odd_card_divisors hm ?_
  rw [Nat.odd_iff, ← sum_divisors_mod_two_eq hodd, ← sigma_one_eq_sum, ← Nat.odd_iff]
  exact h

/-- Splitting off the power of `2`: if `σ(n)` is odd then the odd part `m` of `n` also has
odd `σ(m)`. -/
lemma exists_odd_part_of_odd_sigma {n : ℕ} (hn : n ≠ 0)
    (h : Odd ((ArithmeticFunction.sigma 1) n)) :
    ∃ a m, Odd m ∧ m ≠ 0 ∧ n = 2 ^ a * m ∧ Odd ((ArithmeticFunction.sigma 1) m) := by
  refine ⟨n.factorization 2, ordCompl[2] n, ?_, ?_, ?_, ?_⟩
  · rw [← Nat.not_even_iff_odd, even_iff_two_dvd]
    exact Nat.not_dvd_ordCompl Nat.prime_two hn
  · exact (Nat.ordCompl_pos 2 hn).ne'
  · exact (Nat.ordProj_mul_ordCompl_eq_self n 2).symm
  · have hcop : Nat.Coprime (ordProj[2] n) (ordCompl[2] n) :=
      (Nat.coprime_ordCompl Nat.prime_two hn).pow_left _
    have hmul : (ArithmeticFunction.sigma 1) (ordProj[2] n * ordCompl[2] n)
        = (ArithmeticFunction.sigma 1) (ordProj[2] n) *
            (ArithmeticFunction.sigma 1) (ordCompl[2] n) :=
      (ArithmeticFunction.isMultiplicative_sigma).map_mul_of_coprime hcop
    rw [Nat.ordProj_mul_ordCompl_eq_self] at hmul
    rw [hmul] at h
    exact (Nat.odd_mul.mp h).2

/-- Every quasiperfect number is of the form `2 ^ a * m ^ 2`. -/
lemma Quasiperfect.eq_two_pow_mul_sq {n : ℕ} (h : Quasiperfect n) :
    ∃ a m, n = 2 ^ a * m ^ 2 := by
  obtain ⟨hpos, hsig⟩ := h
  have hodd : Odd ((ArithmeticFunction.sigma 1) n) := by
    rw [hsig]; exact ⟨n, by ring⟩
  obtain ⟨a, m, hm, hm0, rfl, hsm⟩ := exists_odd_part_of_odd_sigma hpos.ne' hodd
  obtain ⟨r, hr⟩ := isSquare_of_odd_of_odd_sigma hm0 hm hsm
  exact ⟨a, r, by rw [hr]; ring⟩

/-- An odd quasiperfect number is a perfect square. -/
lemma Quasiperfect.isSquare_of_odd {n : ℕ} (h : Quasiperfect n) (hodd : Odd n) : IsSquare n := by
  refine isSquare_of_odd_of_odd_sigma h.1.ne' hodd ?_
  rw [h.2]; exact ⟨n, by ring⟩

/-- A quasiperfect number is never squarefree. -/
lemma Quasiperfect.not_squarefree {n : ℕ} (h : Quasiperfect n) : ¬ Squarefree n := by
  intro hs
  obtain ⟨a, m, he⟩ := h.eq_two_pow_mul_sq
  have hm : IsUnit m := hs m ⟨2 ^ a, by rw [he]; ring⟩
  rw [Nat.isUnit_iff] at hm
  rw [he, hm, one_pow, mul_one] at h
  exact not_quasiperfect_prime_pow Nat.prime_two h

/-- A quasiperfect number is not a perfect number. -/
lemma Quasiperfect.not_perfect {n : ℕ} (h : Quasiperfect n) : ¬ n.Perfect := by
  intro hp
  have h2 : ∑ d ∈ n.divisors, d = 2 * n := (Nat.perfect_iff_sum_divisors_eq_two_mul h.1).mp hp
  have h3 := h.2
  rw [sigma_one_eq_sum, h2] at h3
  omega

set_option maxRecDepth 4000 in
/-- There is no quasiperfect number below `101` (verified by kernel computation). -/
lemma not_quasiperfect_of_lt_101 : ∀ n < 101, ¬ Quasiperfect n := by decide

/-- **Conditional reduction for the existence of a quasiperfect number.**

The existence of a quasiperfect number (`σ n = 2 * n + 1`), which is an open problem, is
equivalent to the existence of a quasiperfect number satisfying all the following necessary
conditions: it exceeds `100`, it is not a prime power, it is not squarefree, it has the shape
`2 ^ a * m ^ 2`, and if it is odd then it is a perfect square. -/
theorem QuasiperfectExists :
    (∃ n, Quasiperfect n) ↔
      ∃ n, 100 < n ∧ Quasiperfect n ∧ ¬ IsPrimePow n ∧ ¬ Squarefree n ∧
        (∃ a m, n = 2 ^ a * m ^ 2) ∧ (Odd n → IsSquare n) := by
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_, hn, hn.not_isPrimePow, hn.not_squarefree, hn.eq_two_pow_mul_sq,
      fun ho => hn.isSquare_of_odd ho⟩
    by_contra hle
    exact not_quasiperfect_of_lt_101 n (by omega) hn
  · rintro ⟨n, -, hn, -⟩
    exact ⟨n, hn⟩

end Brockian.QuasiperfectNumbers

