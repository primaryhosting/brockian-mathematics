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
# Hyperperfect Infinitude
Category: Brockian Conjecture
Target: Brockian.HyperperfectNumbers.HyperperfectInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Hyperperfect Infinitude

A number `n > 1` is *`k`-hyperperfect* when `n = 1 + k * (σ(n) - n - 1)`, and
*hyperperfect* when it is `k`-hyperperfect for some `k ≥ 1` (the case `k = 1` is exactly
perfection).  Whether there are infinitely many hyperperfect numbers is open.

This file gives a Lean-checked conditional reduction: `HyperperfectInfinitude` shows that
the infinitude of the prime family `{p prime : p² - p + 1 prime}` implies the infinitude of
hyperperfect numbers, via the construction `p * (p² - p + 1)`, which is `(p-1)`-hyperperfect.
Unconditional instances `6, 21, 301, 2041` are recorded at the end.
-/

namespace Brockian.HyperperfectNumbers

open Finset

/-- The sum-of-divisors function `σ(n) = ∑_{d ∣ n} d`. -/
def sigma (n : ℕ) : ℕ := ∑ d ∈ n.divisors, d

/-- A natural number `n > 1` is *hyperperfect* if it is `k`-hyperperfect for some
`k ≥ 1`, i.e. `n = 1 + k * (σ(n) - n - 1)`.  We phrase the defining equation in a
subtraction-free way as `k * σ(n) + 1 = (k + 1) * n + k`; see
`hyperperfect_iff` for the equivalence with the usual formulation. -/
def Hyperperfect (n : ℕ) : Prop :=
  1 < n ∧ ∃ k : ℕ, 0 < k ∧ k * sigma n + 1 = (k + 1) * n + k

/-- For `n > 1`, both `1` and `n` are divisors of `n`, hence `σ(n) ≥ n + 1`. -/
lemma succ_le_sigma {n : ℕ} (hn : 1 < n) : n + 1 ≤ sigma n := by
  have h1 : (1 : ℕ) ∈ n.divisors := Nat.one_mem_divisors.2 (by omega)
  have hn' : n ∈ n.divisors := Nat.mem_divisors_self n (by omega)
  have hsub : ({1, n} : Finset ℕ) ⊆ n.divisors := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> assumption
  have hmono : ∑ d ∈ ({1, n} : Finset ℕ), d ≤ ∑ d ∈ n.divisors, d :=
    Finset.sum_le_sum_of_subset hsub
  have hsum : ∑ d ∈ ({1, n} : Finset ℕ), d = 1 + n := by
    rw [Finset.sum_insert (by simp; omega), Finset.sum_singleton]
  unfold sigma
  omega

/-- The definition of hyperperfection agrees with the usual formulation
`n = 1 + k * (σ(n) - n - 1)` (with truncated subtraction over `ℕ`). -/
lemma hyperperfect_iff (n : ℕ) :
    Hyperperfect n ↔ 1 < n ∧ ∃ k : ℕ, 0 < k ∧ n = 1 + k * (sigma n - n - 1) := by
  constructor
  · rintro ⟨hn, k, hk, hEq⟩
    refine ⟨hn, k, hk, ?_⟩
    obtain ⟨t, ht⟩ : ∃ t, sigma n = n + 1 + t := ⟨sigma n - (n + 1), by have := succ_le_sigma hn; omega⟩
    have hts : sigma n - n - 1 = t := by omega
    rw [hts]
    rw [ht] at hEq
    have e1 : k * (n + 1 + t) = k * n + k + k * t := by ring
    have e2 : (k + 1) * n = k * n + n := by ring
    omega
  · rintro ⟨hn, k, hk, hEq⟩
    refine ⟨hn, k, hk, ?_⟩
    obtain ⟨t, ht⟩ : ∃ t, sigma n = n + 1 + t := ⟨sigma n - (n + 1), by have := succ_le_sigma hn; omega⟩
    have hts : sigma n - n - 1 = t := by omega
    rw [hts] at hEq
    rw [ht]
    have e1 : k * (n + 1 + t) = k * n + k + k * t := by ring
    have e2 : (k + 1) * n = k * n + n := by ring
    omega

/-- `σ` is multiplicative on the product of two distinct primes. -/
lemma sigma_mul_primes {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    sigma (p * q) = (p + 1) * (q + 1) := by
  have hcop : Nat.Coprime p q := (Nat.coprime_primes hp hq).2 hpq
  unfold sigma
  rw [hcop.sum_divisors_mul, hp.sum_divisors (f := fun d => d),
    hq.sum_divisors (f := fun d => d)]

/-- **Key construction.**  If `p` and `q = p² - p + 1` are both prime, then `p * q`
is `(p-1)`-hyperperfect.  (For `p = 2, 3, 7, 13` this yields `6, 21, 301, 2041`.) -/
lemma hyperperfect_mul_of_prime {p : ℕ} (hp : p.Prime) (hq : (p ^ 2 - p + 1).Prime) :
    Hyperperfect (p * (p ^ 2 - p + 1)) := by
  obtain ⟨m, rfl⟩ : ∃ m, p = m + 2 := ⟨p - 2, by have := hp.two_le; omega⟩
  have hqval : (m + 2) ^ 2 - (m + 2) + 1 = m * m + 3 * m + 3 := by
    have h : (m + 2) ^ 2 = m * m + 4 * m + 4 := by ring
    omega
  rw [hqval] at hq ⊢
  have hne : m + 2 ≠ m * m + 3 * m + 3 := by nlinarith
  refine ⟨by nlinarith, m + 1, by omega, ?_⟩
  rw [sigma_mul_primes hp hq hne]
  ring

/-- **Hyperperfect Infinitude (conditional).**
If there are infinitely many primes `p` for which `p² - p + 1` is also prime,
then there are infinitely many hyperperfect numbers.

The hypothesis is the (open) prime-family assumption; the conclusion is the
Brockian "hyperperfect infinitude" statement.  Unconditionally, `6`, `21`, `301`
and `2041` are hyperperfect (see the examples below). -/
theorem HyperperfectInfinitude
    (H : ∀ N : ℕ, ∃ p : ℕ, N < p ∧ p.Prime ∧ (p ^ 2 - p + 1).Prime) :
    {n : ℕ | Hyperperfect n}.Infinite := by
  apply Set.infinite_of_forall_exists_gt
  intro N
  obtain ⟨p, hNp, hp, hq⟩ := H N
  refine ⟨p * (p ^ 2 - p + 1), hyperperfect_mul_of_prime hp hq, ?_⟩
  calc N < p := hNp
    _ ≤ p * (p ^ 2 - p + 1) := Nat.le_mul_of_pos_right _ (Nat.succ_pos _)

/-- `6` is hyperperfect (indeed perfect: `k = 1`). -/
theorem hyperperfect_six : Hyperperfect 6 := by
  have h := hyperperfect_mul_of_prime (p := 2) (by norm_num) (by norm_num)
  norm_num at h
  exact h

/-- `21` is `2`-hyperperfect. -/
theorem hyperperfect_twentyOne : Hyperperfect 21 := by
  have h := hyperperfect_mul_of_prime (p := 3) (by norm_num) (by norm_num)
  norm_num at h
  exact h

/-- `301` is `6`-hyperperfect. -/
theorem hyperperfect_threeHundredOne : Hyperperfect 301 := by
  have h := hyperperfect_mul_of_prime (p := 7) (by norm_num) (by norm_num)
  norm_num at h
  exact h

/-- `2041` is `12`-hyperperfect. -/
theorem hyperperfect_twoThousandFortyOne : Hyperperfect 2041 := by
  have h := hyperperfect_mul_of_prime (p := 13) (by norm_num) (by norm_num)
  norm_num at h
  exact h

end Brockian.HyperperfectNumbers

#print axioms Brockian.HyperperfectNumbers.HyperperfectInfinitude
#print axioms Brockian.HyperperfectNumbers.hyperperfect_iff
#print axioms Brockian.HyperperfectNumbers.hyperperfect_twoThousandFortyOne

