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

A natural number `n` is *quasiperfect* if `σ(n) = 2n + 1`, i.e. the sum of its proper
divisors is `n + 1`.  No quasiperfect number is known, and their existence is a
long-standing open problem.

This file proves Cattaneo's theorem — every quasiperfect number is an odd perfect
square — and deduces from it the conditional reduction
`Brockian.QuasiperfectNumbers.QuasiperfectExists`: a quasiperfect number exists if and
only if a quasiperfect number that is an odd perfect square exists.
-/

namespace Brockian.QuasiperfectNumbers

open Finset

/-- `sigmaSum n` is the sum of all positive divisors of `n`. -/
def sigmaSum (n : ℕ) : ℕ := ∑ d ∈ n.divisors, d

/-- A natural number is *quasiperfect* if it is positive and the sum of its divisors
is `2n + 1`, i.e. the sum of its *proper* divisors is `n + 1`. -/
def Quasiperfect (n : ℕ) : Prop := 0 < n ∧ sigmaSum n = 2 * n + 1

/-- `sigmaSum` agrees with Mathlib's divisor-sum function `σ 1`. -/
lemma sigmaSum_eq_sigma_one (n : ℕ) : sigmaSum n = ArithmeticFunction.sigma 1 n :=
  (ArithmeticFunction.sigma_one_apply n).symm

lemma sigmaSum_mul_of_coprime {m k : ℕ} (h : Nat.Coprime m k) :
    sigmaSum (m * k) = sigmaSum m * sigmaSum k := by
  simpa [sigmaSum, ArithmeticFunction.sigma_one_apply] using
    (ArithmeticFunction.isMultiplicative_sigma (k := 1)).map_mul_of_coprime h

lemma sigmaSum_two_pow (a : ℕ) : sigmaSum (2 ^ a) = 2 ^ (a + 1) - 1 := by
  rw [sigmaSum, Nat.sum_divisors_prime_pow Nat.prime_two]
  induction a with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, ih]
    have : 1 ≤ 2 ^ (k + 1) := Nat.one_le_two_pow
    ring_nf
    omega

lemma self_le_sigmaSum {n : ℕ} (hn : 0 < n) : n ≤ sigmaSum n :=
  Finset.single_le_sum (f := fun d => d) (by intros; positivity) (Nat.mem_divisors_self n hn.ne')

/-- For odd `x`, the sum of divisors has the same parity as the number of divisors. -/
lemma sigmaSum_mod_two {x : ℕ} (hx : Odd x) :
    sigmaSum x % 2 = x.divisors.card % 2 := by
  rw [sigmaSum, Finset.sum_nat_mod]
  congr 1
  rw [Finset.card_eq_sum_ones]
  refine Finset.sum_congr rfl fun d hd => ?_
  exact Nat.odd_iff.mp (hx.of_dvd_nat (Nat.dvd_of_mem_divisors hd))

lemma isSquare_of_factorization_even {x : ℕ} (hx : x ≠ 0)
    (h : ∀ p, Even (x.factorization p)) : IsSquare x := by
  refine ⟨∏ p ∈ x.primeFactors, p ^ (x.factorization p / 2), ?_⟩
  rw [← Finset.prod_mul_distrib]
  conv_lhs =>
    rw [← Nat.factorization_prod_pow_eq_self hx, Nat.prod_factorization_eq_prod_primeFactors]
  refine Finset.prod_congr rfl fun p _ => ?_
  rw [← pow_add]
  congr 1
  have := Nat.even_iff.mp (h p)
  omega

lemma factorization_even_of_card_divisors_odd {x : ℕ} (hx : x ≠ 0)
    (hcard : Odd x.divisors.card) (p : ℕ) : Even (x.factorization p) := by
  by_contra hodd
  rw [Nat.not_even_iff_odd] at hodd
  have hp : p ∈ x.primeFactors := by
    by_contra hnp
    rw [← Nat.support_factorization, Finsupp.notMem_support_iff] at hnp
    rw [hnp] at hodd
    simp at hodd
  have h2 : 2 ∣ (x.factorization p + 1) := by rcases hodd with ⟨k, hk⟩; omega
  have hdvd : 2 ∣ ∏ q ∈ x.primeFactors, (x.factorization q + 1) :=
    h2.trans (Finset.dvd_prod_of_mem _ hp)
  rw [← Nat.card_divisors hx, Nat.odd_iff] at *
  omega

/-- An odd number whose divisor sum is odd is a perfect square. -/
lemma isSquare_of_odd_of_sigmaSum_odd {x : ℕ} (hx : Odd x) (h : Odd (sigmaSum x)) :
    IsSquare x := by
  have hx0 : x ≠ 0 := by rintro rfl; simp at hx
  have hcard : Odd x.divisors.card := by
    rw [Nat.odd_iff] at h ⊢
    rw [← sigmaSum_mod_two hx]
    exact h
  exact isSquare_of_factorization_even hx0 (factorization_even_of_card_divisors_odd hx0 hcard)

theorem exists_prime_three_mod_four_dvd :
    ∀ m : ℕ, m % 4 = 3 → ∃ p, p.Prime ∧ p % 4 = 3 ∧ p ∣ m := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro hm
    obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd (show m ≠ 1 by omega)
    by_cases h3 : p % 4 = 3
    · exact ⟨p, hp, h3, hpd⟩
    · obtain ⟨k, hk⟩ := hpd
      have hp2 : p % 2 = 1 := by
        rcases hp.eq_two_or_odd with h | h
        · subst h; omega
        · exact h
      have hp4 : p % 4 = 1 := by omega
      have hk4 : k % 4 = 3 := by
        have : m % 4 = (p % 4) * (k % 4) % 4 := by rw [hk, Nat.mul_mod]
        rw [hp4] at this; omega
      have hk0 : 0 < k := by
        rcases Nat.eq_zero_or_pos k with h | h
        · subst h; omega
        · exact h
      have hklt : k < m := by
        rw [hk]; exact (Nat.lt_mul_iff_one_lt_left hk0).mpr hp.one_lt
      obtain ⟨q, hq, hq3, hqd⟩ := ih k hklt hk4
      exact ⟨q, hq, hq3, hqd.trans ⟨p, by rw [hk]; ring⟩⟩

/-- No prime `p ≡ 3 (mod 4)` divides `y ^ 2 + 1`. -/
theorem not_dvd_sq_add_one {p y : ℕ} (hp : p.Prime) (hp3 : p % 4 = 3) : ¬ p ∣ y ^ 2 + 1 := by
  intro hd
  haveI : Fact p.Prime := ⟨hp⟩
  have h0 : ((y ^ 2 + 1 : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ p).mpr hd
  push_cast at h0
  have hsq : IsSquare (-1 : ZMod p) := ⟨y, by linear_combination -h0⟩
  exact (ZMod.exists_sq_eq_neg_one_iff.mp hsq) hp3

/-- **Cattaneo's theorem**: every quasiperfect number is an odd perfect square. -/
theorem odd_and_isSquare_of_quasiperfect {n : ℕ} (h : Quasiperfect n) :
    Odd n ∧ IsSquare n := by
  obtain ⟨hn, heq⟩ := h
  have hn0 : n ≠ 0 := hn.ne'
  set a := n.factorization 2
  set x := n / 2 ^ a
  have hsplit : 2 ^ a * x = n := Nat.ordProj_mul_ordCompl_eq_self n 2
  have hx0 : 0 < x := Nat.ordCompl_pos 2 hn0
  have hxodd : Odd x := by
    rw [Nat.odd_iff, ← Nat.two_dvd_ne_zero]
    exact Nat.not_dvd_ordCompl Nat.prime_two hn0
  have hcop : Nat.Coprime (2 ^ a) x :=
    Nat.Coprime.pow_left _ (Nat.coprime_ordCompl Nat.prime_two hn0)
  obtain ⟨N, hN, hNpos⟩ : ∃ N, 2 ^ (a + 1) = N ∧ 1 ≤ N :=
    ⟨2 ^ (a + 1), rfl, Nat.one_le_two_pow⟩
  -- the fundamental equation `σ(2^a) * σ(x) = 2n + 1`
  have key : (N - 1) * sigmaSum x = N * x + 1 := by
    have h1 := sigmaSum_mul_of_coprime hcop
    rw [hsplit, heq, sigmaSum_two_pow, hN, ← hsplit] at h1
    rw [← h1, ← hN]
    ring
  -- `σ(x)` is odd, hence `x` is a perfect square
  have hSodd : Odd (sigmaSum x) :=
    Nat.Odd.of_mul_right (m := N - 1) ⟨2 ^ a * x, by rw [key, ← hN]; ring⟩
  obtain ⟨y, hy⟩ : IsSquare x := isSquare_of_odd_of_sigmaSum_odd hxodd hSodd
  -- the exponent of `2` in `n` is zero
  have ha0 : a = 0 := by
    by_contra hane
    have h4 : (4 : ℕ) ∣ N := by
      rw [← hN]
      have h2 : (2 : ℕ) ^ 2 ∣ 2 ^ (a + 1) := pow_dvd_pow 2 (by omega)
      simpa using h2
    obtain ⟨c, hc⟩ := h4
    have hT4 : (N - 1) % 4 = 3 := by omega
    -- `N - 1` divides `x + 1`
    have hxS : x ≤ sigmaSum x := self_le_sigmaSum hx0
    obtain ⟨u, hu⟩ : ∃ u, sigmaSum x = x + u := ⟨sigmaSum x - x, by omega⟩
    have h2 : ((N - 1) * (x + u) : ℕ) = (N * x + 1 : ℕ) := by rw [← hu]; exact key
    have h3 : (((N - 1) * (x + u) : ℕ) : ℤ) = ((N * x + 1 : ℕ) : ℤ) := by exact_mod_cast h2
    rw [Nat.cast_mul, Nat.cast_sub hNpos] at h3
    push_cast at h3
    have hTu : (((N - 1) * u : ℕ) : ℤ) = ((x + 1 : ℕ) : ℤ) := by
      rw [Nat.cast_mul, Nat.cast_sub hNpos]
      push_cast
      linarith
    have hTu' : (N - 1) * u = x + 1 := by exact_mod_cast hTu
    obtain ⟨p, hp, hp3, hpd⟩ := exists_prime_three_mod_four_dvd (N - 1) hT4
    refine not_dvd_sq_add_one (y := y) hp hp3 ?_
    have hpx : p ∣ x + 1 := hTu' ▸ hpd.mul_right u
    rwa [hy, ← sq] at hpx
  have hnx : n = x := by rw [← hsplit, ha0, pow_zero, one_mul]
  refine ⟨by rwa [hnx], ?_⟩
  rw [hnx, hy]
  exact ⟨y, rfl⟩

lemma geom_sum_lt_pow {p : ℕ} (hp : 2 ≤ p) (e : ℕ) : ∑ i ∈ Finset.range e, p ^ i < p ^ e := by
  induction e with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, pow_succ]
    have hk : 0 < p ^ k := Nat.pow_pos (by omega)
    nlinarith

/-- A prime power is never quasiperfect. -/
theorem not_quasiperfect_prime_pow {p e : ℕ} (hp : p.Prime) : ¬ Quasiperfect (p ^ e) := by
  rintro ⟨-, heq⟩
  rw [sigmaSum, Nat.sum_divisors_prime_pow hp, Finset.sum_range_succ] at heq
  have := geom_sum_lt_pow hp.two_le e
  omega

set_option maxRecDepth 10000 in
/-- A finite kernel check: there is no quasiperfect number below `200`. -/
theorem not_quasiperfect_of_lt_200 {n : ℕ} (hn : n < 200) : ¬ Quasiperfect n := by
  revert hn
  show n < 200 → ¬ (0 < n ∧ sigmaSum n = 2 * n + 1)
  revert n
  decide

/--
**Conditional reduction for the existence of quasiperfect numbers.**

Whether a quasiperfect number (a number `n` with `σ(n) = 2n + 1`) exists is a
long-standing open problem; no example is known.  What is proved here is the
(nontrivial) reduction of the existence question to the existence of a quasiperfect
number that is moreover an odd perfect square: the two existence statements are
equivalent.
-/
theorem QuasiperfectExists :
    (∃ n : ℕ, Quasiperfect n) ↔ (∃ n : ℕ, Quasiperfect n ∧ Odd n ∧ IsSquare n) := by
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨n, hn, odd_and_isSquare_of_quasiperfect hn⟩
  · rintro ⟨n, hn, -⟩
    exact ⟨n, hn⟩

end Brockian.QuasiperfectNumbers

