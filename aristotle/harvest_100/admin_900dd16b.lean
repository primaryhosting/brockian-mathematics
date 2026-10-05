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

/-!
# Amicable Infinitude
Category: Brockian Conjecture
Target: Brockian.AmicableNumbers.AmicableInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open Finset ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace Brockian.AmicableNumbers

/-- The sum of the proper divisors of `n` (the "aliquot sum"). -/
def sumProperDivisors (n : ℕ) : ℕ := ∑ d ∈ n.properDivisors, d

/-- `m` and `n` form an amicable pair: they are distinct and each is the sum of the
proper divisors of the other. -/
def IsAmicablePair (m n : ℕ) : Prop :=
  m ≠ n ∧ sumProperDivisors m = n ∧ sumProperDivisors n = m

/-- The set of amicable numbers: those belonging to some amicable pair. -/
def AmicableNumbers : Set ℕ := {m | ∃ n, IsAmicablePair m n}

/-- Reformulation of the amicable-pair condition in terms of the divisor-sum function `σ₁`. -/
lemma isAmicablePair_iff_sigma {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) :
    IsAmicablePair m n ↔ m ≠ n ∧ σ 1 m = m + n ∧ σ 1 n = m + n := by
  have hm' : σ 1 m = sumProperDivisors m + m := by
    rw [ArithmeticFunction.sigma_one_apply, sumProperDivisors,
      Nat.sum_divisors_eq_sum_properDivisors_add_self]
  have hn' : σ 1 n = sumProperDivisors n + n := by
    rw [ArithmeticFunction.sigma_one_apply, sumProperDivisors,
      Nat.sum_divisors_eq_sum_properDivisors_add_self]
  unfold IsAmicablePair
  rw [hm', hn']
  omega

/-- `σ₁` of a power of two. -/
lemma sigma_one_two_pow (k : ℕ) : σ 1 (2 ^ k) + 1 = 2 ^ (k + 1) := by
  rw [ArithmeticFunction.sigma_one_apply_prime_pow Nat.prime_two]
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ]
    ring_nf
    ring_nf at ih
    omega

/-- `σ₁` of a prime. -/
lemma sigma_one_prime {p : ℕ} (hp : p.Prime) : σ 1 p = p + 1 := by
  have := ArithmeticFunction.sigma_one_apply_prime_pow (p := p) (i := 1) hp
  simpa [Finset.sum_range_succ, add_comm] using this

/-- **Thabit ibn Qurra's rule.** If `a = 2 ^ n` with `n ≥ 1` and the three numbers
`p = 3a - 1`, `q = 6a - 1`, `r = 18a² - 1` are all prime, then `2a·p·q` and `2a·r`
form an amicable pair. -/
theorem thabit_amicable {n a p q r : ℕ} (hn : 1 ≤ n) (ha : a = 2 ^ n)
    (hp : p.Prime) (hpv : p + 1 = 3 * a)
    (hq : q.Prime) (hqv : q + 1 = 6 * a)
    (hr : r.Prime) (hrv : r + 1 = 18 * a ^ 2) :
    IsAmicablePair (2 * a * p * q) (2 * a * r) := by
  -- basic size facts
  have ha2 : 2 ≤ a := by
    subst ha
    calc 2 = 2 ^ 1 := by norm_num
    _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hpne : p ≠ 2 := by omega
  have hqne : q ≠ 2 := by omega
  have hrne : r ≠ 2 := by nlinarith
  have hpq : p ≠ q := by omega
  -- coprimality
  have hcop2 : ∀ {x : ℕ}, x.Prime → x ≠ 2 → Nat.Coprime (2 ^ (n + 1)) x := by
    intro x hx hx2
    exact Nat.Coprime.pow_left _ ((Nat.coprime_primes Nat.prime_two hx).mpr (Ne.symm hx2))
  have hcpq : Nat.Coprime p q := (Nat.coprime_primes hp hq).mpr hpq
  have h2a : 2 * a = 2 ^ (n + 1) := by rw [ha]; ring
  -- the divisor sum of the power of two
  set S := σ 1 (2 ^ (n + 1)) with hS
  have hSv : S + 1 = 4 * a := by
    have h := sigma_one_two_pow (n + 1)
    rw [← hS] at h
    rw [ha]
    calc S + 1 = 2 ^ (n + 1 + 1) := h
    _ = 4 * 2 ^ n := by ring
  -- σ of the two members
  have hM : σ 1 (2 * a * p * q) = S * (p + 1) * (q + 1) := by
    rw [h2a, mul_assoc, mul_assoc,
      ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime
        (Nat.Coprime.mul_right (hcop2 hp hpne) (hcop2 hq hqne)),
      ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcpq,
      sigma_one_prime hp, sigma_one_prime hq, ← hS, mul_assoc]
  have hN : σ 1 (2 * a * r) = S * (r + 1) := by
    rw [h2a, ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (hcop2 hr hrne),
      sigma_one_prime hr, ← hS]
  -- the key arithmetic identity
  have key : 2 * a * p * q + 2 * a * r = 18 * a ^ 2 * S := by
    have hp' : p = 3 * a - 1 := by omega
    have hq' : q = 6 * a - 1 := by omega
    have h3 : 1 ≤ 18 * a ^ 2 := by nlinarith
    have hr' : r = 18 * a ^ 2 - 1 := by omega
    have hS' : S = 4 * a - 1 := by omega
    have h1 : 1 ≤ 3 * a := by omega
    have h2 : 1 ≤ 6 * a := by omega
    have h4 : 1 ≤ 4 * a := by omega
    zify [h1, h2, h3, h4] at hp' hq' hr' hS' ⊢
    rw [hp', hq', hr', hS']
    ring
  have hne : 2 * a * p * q ≠ 2 * a * r := by
    have hpqr : p * q ≠ r := by nlinarith
    intro h
    rw [mul_assoc] at h
    exact hpqr (Nat.eq_of_mul_eq_mul_left (by omega) h)
  have hMne : 2 * a * p * q ≠ 0 := by positivity
  have hNne : 2 * a * r ≠ 0 := by positivity
  rw [isAmicablePair_iff_sigma hMne hNne]
  refine ⟨hne, ?_, ?_⟩
  · rw [hM, hpv, hqv, key]
    ring
  · rw [hN, hrv, key]
    ring

/-- `n` is a *Thabit index* when Thabit's rule applies at `n`, i.e. the three numbers
`3·2ⁿ - 1`, `3·2ⁿ⁺¹ - 1`, `9·2²ⁿ⁺¹ - 1` are all prime. -/
def IsThabitIndex (n : ℕ) : Prop :=
  1 ≤ n ∧ (3 * 2 ^ n - 1).Prime ∧ (3 * 2 ^ (n + 1) - 1).Prime ∧ (9 * 2 ^ (2 * n + 1) - 1).Prime

/-- A set of naturals that contains arbitrarily large elements is infinite. -/
lemma infinite_of_unbounded {s : Set ℕ} (h : ∀ N : ℕ, ∃ m ∈ s, N < m) : s.Infinite := by
  apply Set.infinite_of_not_bddAbove
  rintro ⟨B, hB⟩
  obtain ⟨m, hm, hlt⟩ := h B
  exact absurd (hB hm) (by omega)

/-- The set of amicable numbers is infinite iff it contains arbitrarily large elements. -/
theorem amicable_infinite_iff_unbounded :
    AmicableNumbers.Infinite ↔ ∀ N : ℕ, ∃ m ∈ AmicableNumbers, N < m := by
  constructor
  · intro h N
    obtain ⟨m, hm, hlt⟩ := h.exists_gt N
    exact ⟨m, hm, hlt⟩
  · exact infinite_of_unbounded

/-- Thabit's rule produces amicable numbers at every Thabit index. -/
theorem thabit_mem_amicableNumbers {n : ℕ} (hn : IsThabitIndex n) :
    2 ^ (n + 1) * ((3 * 2 ^ n - 1) * (3 * 2 ^ (n + 1) - 1)) ∈ AmicableNumbers := by
  obtain ⟨h1, hp, hq, hr⟩ := hn
  have hpow : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  refine ⟨2 ^ (n + 1) * (9 * 2 ^ (2 * n + 1) - 1), ?_⟩
  have hrw : 2 ^ (n + 1) * ((3 * 2 ^ n - 1) * (3 * 2 ^ (n + 1) - 1))
      = 2 * 2 ^ n * (3 * 2 ^ n - 1) * (3 * 2 ^ (n + 1) - 1) := by ring
  have hrw2 : 2 ^ (n + 1) * (9 * 2 ^ (2 * n + 1) - 1)
      = 2 * 2 ^ n * (9 * 2 ^ (2 * n + 1) - 1) := by ring
  rw [hrw, hrw2]
  have hpow1 : 2 ^ (n + 1) = 2 * 2 ^ n := by ring
  have h9 : 9 * 2 ^ (2 * n + 1) = 18 * (2 ^ n) ^ 2 := by
    rw [← pow_mul]
    ring
  exact thabit_amicable h1 rfl hp (by omega) hq (by omega) hr (by omega)

/-- **Conditional infinitude of amicable numbers.**
If there are infinitely many Thabit indices — that is, if for every `N` there is some `n ≥ N`
with `3·2ⁿ - 1`, `3·2ⁿ⁺¹ - 1` and `9·2²ⁿ⁺¹ - 1` all prime — then there are infinitely many
amicable numbers. -/
theorem AmicableInfinitude (h : ∀ N : ℕ, ∃ n, N ≤ n ∧ IsThabitIndex n) :
    AmicableNumbers.Infinite := by
  apply infinite_of_unbounded
  intro N
  obtain ⟨n, hNn, hn⟩ := h N
  refine ⟨_, thabit_mem_amicableNumbers hn, ?_⟩
  have hpow : n < 2 ^ n := Nat.lt_two_pow_self
  have hp1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  have hp2 : 1 ≤ 2 ^ (n + 1) := Nat.one_le_two_pow
  have h1 : 1 ≤ (3 * 2 ^ n - 1) * (3 * 2 ^ (n + 1) - 1) :=
    Nat.mul_le_mul (by omega) (by omega)
  have hfin : 2 ^ n ≤ 2 ^ (n + 1) * ((3 * 2 ^ n - 1) * (3 * 2 ^ (n + 1) - 1)) := by
    calc 2 ^ n ≤ 2 ^ (n + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    _ = 2 ^ (n + 1) * 1 := by ring
    _ ≤ _ := Nat.mul_le_mul_left _ h1
  omega

/-- The classical amicable pair `(220, 284)`, obtained from Thabit's rule at `n = 1`. -/
theorem amicable_220_284 : IsAmicablePair 220 284 := by
  have h := thabit_amicable (n := 1) (a := 2) (p := 5) (q := 11) (r := 71)
    le_rfl (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  norm_num at h
  exact h

/-- Amicable numbers exist. -/
theorem amicableNumbers_nonempty : AmicableNumbers.Nonempty :=
  ⟨220, 284, amicable_220_284⟩

end Brockian.AmicableNumbers

