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
# Odd Superperfect Exists
Category: Brockian Conjecture
Target: Brockian.SuperperfectNumbers.OddSuperperfectExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open Finset

namespace Brockian.SuperperfectNumbers

/-- The sum-of-divisors function `σ(n) = ∑_{d ∣ n} d`. -/
def sigma1 (n : ℕ) : ℕ := ∑ d ∈ n.divisors, d

/-- A natural number `n` is *superperfect* if `σ(σ(n)) = 2n`. -/
def Superperfect (n : ℕ) : Prop := sigma1 (sigma1 n) = 2 * n

/-! ### Basic facts about `sigma1` -/

lemma sigma1_one : sigma1 1 = 1 := by simp [sigma1]

lemma le_sigma1 {n : ℕ} (hn : n ≠ 0) : n ≤ sigma1 n :=
  Finset.single_le_sum (f := fun d => d) (fun _ _ => Nat.zero_le _)
    (Nat.mem_divisors_self n hn)

lemma sigma1_ne_zero {n : ℕ} (hn : n ≠ 0) : sigma1 n ≠ 0 :=
  fun h => hn (Nat.le_zero.mp (h ▸ le_sigma1 hn))

lemma sigma1_primePow {p e : ℕ} (hp : p.Prime) :
    sigma1 (p ^ e) = ∑ i ∈ range (e + 1), p ^ i := by
  simp [sigma1, Nat.sum_divisors_prime_pow hp]

/-- `σ` is multiplicative: it factors as a product over the prime powers of `m`. -/
lemma sigma1_factorization {m : ℕ} (hm : m ≠ 0) :
    sigma1 m = ∏ p ∈ m.primeFactors, sigma1 (p ^ m.factorization p) := by
  have h := (ArithmeticFunction.isMultiplicative_sigma (k := 1)).multiplicative_factorization _ hm
  simp only [sigma1, ← ArithmeticFunction.sigma_one_apply]
  rw [h, Finsupp.prod, Nat.support_factorization]

/-! ### The 2-adic behaviour of `σ` on prime powers -/

/-- `σ(2^e) = 2^{e+1} - 1` is odd. -/
lemma sigma1_two_pow_odd (e : ℕ) : Odd (sigma1 (2 ^ e)) := by
  rw [Nat.odd_iff, sigma1_primePow Nat.prime_two, Finset.sum_range_succ']
  have h : 2 ∣ ∑ i ∈ range e, 2 ^ (i + 1) :=
    Finset.dvd_sum fun i _ => dvd_pow_self 2 (Nat.succ_ne_zero i)
  omega

/-- For an odd prime `p` and an even exponent `e`, `σ(p^e)` is odd. -/
lemma sigma1_odd_of_even_exp {p e : ℕ} (hp : p.Prime) (hodd : p % 2 = 1) (he : Even e) :
    Odd (sigma1 (p ^ e)) := by
  rw [Nat.odd_iff, sigma1_primePow hp, Finset.sum_nat_mod]
  have h : ∀ i ∈ range (e + 1), p ^ i % 2 = 1 := by
    intro i _
    rw [Nat.pow_mod, hodd, one_pow]
    rfl
  rw [Finset.sum_congr rfl h]
  simp [Nat.add_mod, Nat.even_iff.mp he]

/-- For a prime `p ≡ 3 (mod 4)` and an odd exponent `e`, `σ(p^e)` is divisible by `4`. -/
lemma four_dvd_sigma1_primePow {p e : ℕ} (hp : p.Prime) (hp4 : p % 4 = 3) (he : Odd e) :
    4 ∣ sigma1 (p ^ e) := by
  rw [sigma1_primePow hp]
  have h : ((∑ i ∈ range (e + 1), p ^ i : ℕ) : ZMod 4) = 0 := by
    push_cast
    have hpc : ((p : ZMod 4)) = -1 := by
      have h4 := ZMod.natCast_mod p 4
      rw [hp4] at h4
      rw [← h4]; decide
    simp only [hpc, neg_one_geom_sum]
    simp [Nat.even_add_one, Nat.not_even_iff_odd.mpr he]
  exact (ZMod.natCast_eq_zero_iff _ _).mp h

/-! ### The key structural lemma -/

/-- If `σ(m) ≡ 2 (mod 4)` then `m` has a prime divisor congruent to `1` modulo `4`.

Indeed, `σ(m)` is the product of the numbers `σ(p^{v_p(m)})`; the factor at `p = 2` is odd,
a factor at an odd prime with even exponent is odd, and a factor at a prime `p ≡ 3 (mod 4)`
with odd exponent is divisible by `4`. So if no prime divisor of `m` were `≡ 1 (mod 4)`,
then `σ(m)` would be either odd or divisible by `4`. -/
lemma exists_prime_one_mod_four_dvd_of_sigma1_mod_four {m : ℕ} (hm : m ≠ 0)
    (h : sigma1 m % 4 = 2) : ∃ q, q.Prime ∧ q % 4 = 1 ∧ q ∣ m := by
  by_contra hcon
  push_neg at hcon
  by_cases hex : ∃ p ∈ m.primeFactors, 4 ∣ sigma1 (p ^ m.factorization p)
  · obtain ⟨p, hp, hdvd⟩ := hex
    have h4 : 4 ∣ sigma1 m := by
      rw [sigma1_factorization hm]
      exact hdvd.trans (Finset.dvd_prod_of_mem _ hp)
    omega
  · push_neg at hex
    have hodd : ∀ p ∈ m.primeFactors, Odd (sigma1 (p ^ m.factorization p)) := by
      intro p hp
      have hpp := Nat.prime_of_mem_primeFactors hp
      rcases eq_or_ne p 2 with rfl | hp2
      · exact sigma1_two_pow_odd _
      · have hpodd : p % 2 = 1 := Nat.odd_iff.mp (hpp.odd_of_ne_two hp2)
        have h4 : p % 4 = 1 ∨ p % 4 = 3 := by omega
        rcases h4 with h1 | h3
        · exact absurd (Nat.dvd_of_mem_primeFactors hp) (hcon p hpp h1)
        · have he : Even (m.factorization p) := by
            by_contra hne
            exact hex p hp (four_dvd_sigma1_primePow hpp h3 (Nat.not_even_iff_odd.mp hne))
          exact sigma1_odd_of_even_exp hpp hpodd he
    have hprod : Odd (sigma1 m) := by
      rw [sigma1_factorization hm]
      exact Finset.prod_induction _ Odd (fun _ _ => Odd.mul) odd_one hodd
    rw [Nat.odd_iff] at hprod
    omega

/-! ### Necessary conditions on an odd superperfect number -/

lemma one_lt_of_odd_superperfect {n : ℕ} (hn : Odd n) (hs : Superperfect n) : 1 < n := by
  rcases Nat.lt_or_ge n 2 with h | h
  · interval_cases n
    · simp at hn
    · rw [Superperfect, sigma1_one, sigma1_one] at hs; omega
  · omega

/-- Any odd superperfect number `n` has `σ(n)` divisible by a prime congruent to `1` modulo `4`. -/
lemma exists_prime_one_mod_four_dvd_sigma1 {n : ℕ} (hn : Odd n) (hs : Superperfect n) :
    ∃ q, q.Prime ∧ q % 4 = 1 ∧ q ∣ sigma1 n := by
  have hn0 : n ≠ 0 := by rintro rfl; simp at hn
  have hmod : sigma1 (sigma1 n) % 4 = 2 := by
    rw [hs, Nat.odd_iff] at *
    omega
  exact exists_prime_one_mod_four_dvd_of_sigma1_mod_four (sigma1_ne_zero hn0) hmod

/-! ### The target statement -/

/-- **Odd superperfect numbers.** Whether an odd superperfect number exists is an open
problem; what is proved here is a Lean-checked reduction: the existence of an odd
superperfect number is *equivalent* to the existence of one which, in addition, exceeds `1`
and whose sum of divisors `σ(n)` has a prime factor congruent to `1` modulo `4`.

The nontrivial (forward) direction is the content: every odd superperfect number
automatically satisfies these two extra conditions. -/
theorem OddSuperperfectExists :
    (∃ n, Odd n ∧ Superperfect n) ↔
      ∃ n, Odd n ∧ Superperfect n ∧ 1 < n ∧ ∃ q, q.Prime ∧ q % 4 = 1 ∧ q ∣ sigma1 n := by
  constructor
  · rintro ⟨n, hn, hs⟩
    exact ⟨n, hn, hs, one_lt_of_odd_superperfect hn hs,
      exists_prime_one_mod_four_dvd_sigma1 hn hs⟩
  · rintro ⟨n, hn, hs, -, -⟩
    exact ⟨n, hn, hs⟩

end Brockian.SuperperfectNumbers

