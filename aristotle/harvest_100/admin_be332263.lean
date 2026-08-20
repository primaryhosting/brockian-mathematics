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

/-!
# Odd Superperfect Exists
Category: Brockian Conjecture
Target: Brockian.SuperperfectNumbers.OddSuperperfectExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

A natural number `n` is *superperfect* when `σ (σ n) = 2 n`.  Suryanarayana and Kanold
showed that the even superperfect numbers are exactly the powers `2 ^ k` with
`2 ^ (k + 1) - 1` prime; whether an *odd* superperfect number exists is an open problem.

This file contains a Lean-checked reduction of that open problem, together with the
(easy half of the) even classification and two unconditional constraints on a
hypothetical odd superperfect number.
-/

open scoped ArithmeticFunction.sigma

open ArithmeticFunction Finset

namespace Brockian.SuperperfectNumbers

/-- A natural number `n` is *superperfect* if `σ (σ n) = 2 * n`, where `σ` is the
sum-of-divisors function. -/
def Superperfect (n : ℕ) : Prop := σ 1 (σ 1 n) = 2 * n

lemma superperfect_iff (n : ℕ) :
    Superperfect n ↔ (∑ d ∈ (∑ d ∈ n.divisors, d).divisors, d) = 2 * n := by
  rw [Superperfect, sigma_one_apply, sigma_one_apply]

/-- The easy half of the classification of even superperfect numbers: if `2 ^ (k+1) - 1`
is prime, then `2 ^ k` is superperfect. -/
theorem superperfect_two_pow_of_mersenne_prime {k : ℕ}
    (hp : Nat.Prime (2 ^ (k + 1) - 1)) : Superperfect (2 ^ k) := by
  rw [Superperfect, sigma_one_apply_prime_pow Nat.prime_two]
  rw [show ∑ i ∈ range (k + 1), 2 ^ i = 2 ^ (k + 1) - 1 by
    simpa using Nat.geomSum_eq (le_refl 2) (k + 1)]
  rw [sigma_one_apply, hp.divisors, Finset.sum_pair hp.one_lt.ne]
  have h1 : 1 ≤ 2 ^ (k + 1) := Nat.one_le_two_pow
  have h2 : 2 ^ (k + 1) = 2 * 2 ^ k := by ring
  omega

/-! ### Parity of the sum-of-divisors function -/

private lemma odd_geom_even {p : ℕ} (hp : Even p) (m : ℕ) :
    Odd (∑ i ∈ range (m + 1), p ^ i) := by
  induction m with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ]
      exact ih.add_even ((Nat.even_pow).2 ⟨hp, by omega⟩)

private lemma odd_geom_odd {p : ℕ} (hp : Odd p) {m : ℕ} (hm : Even m) :
    Odd (∑ i ∈ range (m + 1), p ^ i) := by
  have h : (∑ i ∈ range (m + 1), p ^ i) % 2 = (∑ i ∈ range (m + 1), (p ^ i % 2)) % 2 :=
    Finset.sum_nat_mod _ _ _
  have h2 : ∀ i ∈ range (m + 1), p ^ i % 2 = 1 := fun i _ => Nat.odd_iff.mp hp.pow
  rw [Finset.sum_congr rfl h2] at h
  simp at h
  obtain ⟨t, rfl⟩ := hm
  rw [Nat.odd_iff, h]
  omega

/-- If every odd prime occurs to an even power in `m`, then `σ m` is odd.  (Equivalently:
`σ m` is odd exactly when `m` is a square or twice a square.) -/
lemma odd_sigma_of_even_factorization {m : ℕ} (hm : m ≠ 0)
    (h : ∀ p ∈ m.primeFactors, p ≠ 2 → Even (m.factorization p)) : Odd (σ 1 m) := by
  rw [sigma_eq_prod_primeFactors_sum_range_factorization_pow_mul hm]
  apply Finset.prod_induction _ Odd (fun a b ha hb => ha.mul hb) odd_one
  intro p hp
  simp only [mul_one]
  rcases eq_or_ne p 2 with rfl | hne
  · exact odd_geom_even (by decide) _
  · exact odd_geom_odd (Nat.Prime.odd_of_ne_two (Nat.prime_of_mem_primeFactors hp) hne)
      (h p hp hne)

/-! ### Constraints on a hypothetical odd superperfect number -/

/-- For an odd superperfect number `n`, some odd prime divides `σ n` to an odd power.
In particular `σ n` is neither a perfect square nor twice a perfect square. -/
lemma exists_odd_prime_odd_exponent {n : ℕ} (hn : Odd n) (h : Superperfect n) :
    ∃ p, p.Prime ∧ p ≠ 2 ∧ Odd ((σ 1 n).factorization p) := by
  by_contra hcon
  push_neg at hcon
  have hn0 : n ≠ 0 := hn.pos.ne'
  have hM0 : σ 1 n ≠ 0 := fun hz => hn0 (sigma_eq_zero.mp hz)
  have hodd : Odd (σ 1 (σ 1 n)) := by
    refine odd_sigma_of_even_factorization hM0 ?_
    intro p hp hne
    exact Nat.not_odd_iff_even.1 (hcon p (Nat.prime_of_mem_primeFactors hp) hne)
  rw [h] at hodd
  exact (Nat.not_odd_iff_even.2 (even_two_mul n)) hodd

set_option maxRecDepth 8000000 in
private lemma check_lt_1000 :
    ∀ n ∈ Finset.range 1000, n % 2 = 1 →
      (∑ d ∈ (∑ d ∈ n.divisors, d).divisors, d) ≠ 2 * n := by
  decide +kernel

/-- No odd number below `1000` is superperfect. -/
lemma not_superperfect_of_lt {n : ℕ} (hn : Odd n) (hlt : n < 1000) : ¬ Superperfect n := by
  rw [superperfect_iff]
  exact check_lt_1000 n (Finset.mem_range.2 hlt) (Nat.odd_iff.mp hn)

/-- **Odd superperfect numbers.**  Whether an odd superperfect number exists is an open
problem; the following is a Lean-checked reduction.  An odd superperfect number exists if
and only if there is one that exceeds `1000` and whose sum of divisors `σ n` is divisible
by an odd prime to an odd power (equivalently, `σ n` is neither a square nor twice a
square). -/
theorem OddSuperperfectExists :
    (∃ n, Odd n ∧ Superperfect n) ↔
      ∃ n, 1000 < n ∧ Odd n ∧ Superperfect n ∧
        ∃ p, p.Prime ∧ p ≠ 2 ∧ Odd ((σ 1 n).factorization p) := by
  constructor
  · rintro ⟨n, hn, h⟩
    rcases lt_or_ge 1000 n with h1 | h1
    · exact ⟨n, h1, hn, h, exists_odd_prime_odd_exponent hn h⟩
    · have hlt : n < 1000 :=
        lt_of_le_of_ne h1 (by rintro rfl; exact (Nat.not_odd_iff_even.2 (by decide)) hn)
      exact absurd h (not_superperfect_of_lt hn hlt)
  · rintro ⟨n, _, hn, h, _⟩
    exact ⟨n, hn, h⟩

end Brockian.SuperperfectNumbers

