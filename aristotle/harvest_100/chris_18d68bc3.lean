import Brockian.AmicableNumbers

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
# Amicable Infinitude
Category: Brockian Conjecture
Target: Brockian.AmicableNumbers.AmicableInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Amicable Infinitude
Category: Brockian Conjecture
Target: Brockian.AmicableNumbers.AmicableInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.AmicableNumbers

open Finset

/-- `a` and `b` form an *amicable pair*: they are distinct and each is the sum of the
proper divisors of the other, equivalently `σ₁ a = σ₁ b = a + b`. -/
def Amicable (a b : ℕ) : Prop :=
  a ≠ b ∧ (∑ d ∈ a.divisors, d) = a + b ∧ (∑ d ∈ b.divisors, d) = a + b

/-- A natural number is *amicable* if it belongs to some amicable pair. -/
def IsAmicable (a : ℕ) : Prop := ∃ b, Amicable a b

/-- The hypothesis of Euler's rule (Thābit ibn Qurra's rule) at parameter `m`
(corresponding to the classical index `n = m + 2`):
the three numbers `3·2^(m+1) - 1`, `3·2^(m+2) - 1` and `9·2^(2m+3) - 1` are all prime. -/
def EulerRulePrimes (m : ℕ) : Prop :=
  Nat.Prime (3 * 2 ^ (m + 1) - 1) ∧ Nat.Prime (3 * 2 ^ (m + 2) - 1) ∧
    Nat.Prime (9 * 2 ^ (2 * m + 3) - 1)

/-! ### Elementary divisor-sum computations -/

theorem sum_divisors_two_pow (k : ℕ) : (∑ d ∈ (2 ^ k).divisors, d) + 1 = 2 ^ (k + 1) := by
  rw [← ArithmeticFunction.sigma_one_apply,
    ArithmeticFunction.sigma_one_apply_prime_pow Nat.prime_two]
  induction k with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ]
      have h : 2 ^ (n + 1 + 1) = 2 * 2 ^ (n + 1) := by ring
      omega

theorem sum_divisors_prime {p : ℕ} (hp : p.Prime) : (∑ d ∈ p.divisors, d) = p + 1 := by
  rw [hp.divisors, Finset.sum_pair hp.one_lt.ne]
  omega

/-! ### Euler's rule -/

/-- **Euler's rule** (generalising Thābit ibn Qurra's rule): if `p = 3·2^(m+1) - 1`,
`q = 3·2^(m+2) - 1` and `r = 9·2^(2m+3) - 1` are all prime, then `2^(m+2)·p·q` and
`2^(m+2)·r` form an amicable pair. -/
theorem amicable_of_eulerRulePrimes {m : ℕ} (h : EulerRulePrimes m) :
    Amicable (2 ^ (m + 2) * ((3 * 2 ^ (m + 1) - 1) * (3 * 2 ^ (m + 2) - 1)))
      (2 ^ (m + 2) * (9 * 2 ^ (2 * m + 3) - 1)) := by
  obtain ⟨hp, hq, hr⟩ := h
  -- write `2 ^ (m + 1) = Q + 2`
  have h2 : 2 ≤ 2 ^ (m + 1) := by
    calc (2:ℕ) = 2 ^ 1 := (pow_one 2).symm
    _ ≤ 2 ^ (m + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  obtain ⟨Q, hQ⟩ : ∃ Q, 2 ^ (m + 1) = Q + 2 := ⟨2 ^ (m + 1) - 2, by omega⟩
  have e2 : 2 ^ (m + 2) = 2 * (Q + 2) := by
    rw [show m + 2 = (m + 1) + 1 from rfl, pow_succ, hQ]; ring
  have e3 : 2 ^ (2 * m + 3) = 2 * ((Q + 2) * (Q + 2)) := by
    have : (2:ℕ) ^ (2 * m + 3) = 2 ^ (m + 1) * 2 ^ (m + 1) * 2 := by ring
    rw [this, hQ]; ring
  have hpv : 3 * 2 ^ (m + 1) - 1 = 3 * Q + 5 := by rw [hQ]; omega
  have hqv : 3 * 2 ^ (m + 2) - 1 = 6 * Q + 11 := by rw [e2]; omega
  have hrv : 9 * 2 ^ (2 * m + 3) - 1 = 18 * Q * Q + 72 * Q + 71 := by
    have h9 : 9 * (2 * ((Q + 2) * (Q + 2))) = 18 * Q * Q + 72 * Q + 72 := by ring
    rw [e3]; omega
  -- divisor sums
  have hs2 : (∑ d ∈ (2 ^ (m + 2)).divisors, d) = 4 * Q + 7 := by
    have := sum_divisors_two_pow (m + 2)
    have h4 : (2:ℕ) ^ (m + 2 + 1) = 4 * (Q + 2) := by
      rw [show m + 2 + 1 = (m + 1) + 2 from rfl, pow_succ, pow_succ, hQ]; ring
    omega
  -- coprimality facts
  have hodd : ∀ {x : ℕ}, x.Prime → x % 2 = 1 → Nat.Coprime (2 ^ (m + 2)) x := by
    intro x hx hx2
    refine Nat.Coprime.pow_left _ ?_
    rw [Nat.coprime_comm]
    exact (Nat.coprime_primes hx Nat.prime_two).mpr (by omega)
  have hcp : Nat.Coprime (2 ^ (m + 2)) (3 * 2 ^ (m + 1) - 1) := by
    refine hodd hp ?_
    rw [hpv]; omega
  have hcq : Nat.Coprime (2 ^ (m + 2)) (3 * 2 ^ (m + 2) - 1) := by
    refine hodd hq ?_
    rw [hqv]; omega
  have hcr : Nat.Coprime (2 ^ (m + 2)) (9 * 2 ^ (2 * m + 3) - 1) := by
    refine hodd hr ?_
    rw [hrv]; omega
  have hpq : Nat.Coprime (3 * 2 ^ (m + 1) - 1) (3 * 2 ^ (m + 2) - 1) := by
    refine (Nat.coprime_primes hp hq).mpr ?_
    rw [hpv, hqv]; omega
  -- the two divisor sums
  have hsa : (∑ d ∈ (2 ^ (m + 2) * ((3 * 2 ^ (m + 1) - 1) * (3 * 2 ^ (m + 2) - 1))).divisors, d)
      = (4 * Q + 7) * ((3 * Q + 6) * (6 * Q + 12)) := by
    rw [Nat.Coprime.sum_divisors_mul (hcp.mul_right hcq),
      Nat.Coprime.sum_divisors_mul hpq, hs2, sum_divisors_prime hp, sum_divisors_prime hq,
      hpv, hqv]
  have hsb : (∑ d ∈ (2 ^ (m + 2) * (9 * 2 ^ (2 * m + 3) - 1)).divisors, d)
      = (4 * Q + 7) * (18 * Q * Q + 72 * Q + 72) := by
    rw [Nat.Coprime.sum_divisors_mul hcr, hs2, sum_divisors_prime hr, hrv]
  refine ⟨?_, ?_, ?_⟩
  · rw [hpv, hqv, hrv, e2]
    have hlt : (3 * Q + 5) * (6 * Q + 11) < 18 * Q * Q + 72 * Q + 71 := by nlinarith
    exact Nat.ne_of_lt (mul_lt_mul_of_pos_left hlt (show 0 < 2 * (Q + 2) by omega))
  · rw [hsa, hpv, hqv, hrv, e2]; ring
  · rw [hsb, hpv, hqv, hrv, e2]; ring

/-! ### Sanity checks: the classical amicable pairs produced by Euler's rule -/

theorem eulerRulePrimes_zero : EulerRulePrimes 0 := by
  refine ⟨?_, ?_, ?_⟩ <;> norm_num

/-- The classical pair `(220, 284)` is the instance `m = 0` of Euler's rule. -/
theorem amicable_220_284 : Amicable 220 284 := by
  have h := amicable_of_eulerRulePrimes eulerRulePrimes_zero
  norm_num at h
  exact h

theorem eulerRulePrimes_two : EulerRulePrimes 2 := by
  refine ⟨?_, ?_, ?_⟩ <;> norm_num

/-- The pair `(17296, 18416)` is the instance `m = 2` of Euler's rule. -/
theorem amicable_17296_18416 : Amicable 17296 18416 := by
  have h := amicable_of_eulerRulePrimes eulerRulePrimes_two
  norm_num at h
  exact h

/-! ### The conditional infinitude statement -/

/-- An equivalent reformulation of the infinitude of amicable numbers: the set of amicable
numbers is infinite iff it is unbounded. -/
theorem infinite_isAmicable_iff_unbounded :
    {a : ℕ | IsAmicable a}.Infinite ↔ ∀ N : ℕ, ∃ a, N < a ∧ IsAmicable a := by
  constructor
  · intro h N
    obtain ⟨a, ha, haN⟩ := h.exists_gt N
    exact ⟨a, haN, ha⟩
  · intro h
    refine Set.infinite_of_forall_exists_gt fun N => ?_
    obtain ⟨a, haN, ha⟩ := h N
    exact ⟨a, ha, haN⟩

/-- **Conditional reduction of the amicable-number infinitude problem.**
If there are infinitely many parameters `m` satisfying the hypothesis of Euler's rule
(i.e. infinitely many `n = m + 2` for which `3·2^(n-1) - 1`, `3·2^n - 1` and `9·2^(2n-1) - 1`
are simultaneously prime), then there are infinitely many amicable numbers. -/
theorem AmicableInfinitude (h : {m : ℕ | EulerRulePrimes m}.Infinite) :
    {a : ℕ | IsAmicable a}.Infinite := by
  apply Set.infinite_of_forall_exists_gt
  intro N
  obtain ⟨m, hm, hmN⟩ := h.exists_gt N
  refine ⟨2 ^ (m + 2) * ((3 * 2 ^ (m + 1) - 1) * (3 * 2 ^ (m + 2) - 1)),
    ⟨2 ^ (m + 2) * (9 * 2 ^ (2 * m + 3) - 1), amicable_of_eulerRulePrimes hm⟩, ?_⟩
  · have hpos : 1 ≤ (3 * 2 ^ (m + 1) - 1) * (3 * 2 ^ (m + 2) - 1) := by
      have h1 : 2 ≤ 2 ^ (m + 1) := Nat.one_lt_two_pow (by omega)
      have h2 : 2 ≤ 2 ^ (m + 2) := Nat.one_lt_two_pow (by omega)
      have h3 : 1 ≤ 3 * 2 ^ (m + 1) - 1 := by omega
      have h4 : 1 ≤ 3 * 2 ^ (m + 2) - 1 := by omega
      nlinarith
    calc N < m := hmN
    _ < 2 ^ (m + 2) := by
        have hm1 : m < 2 ^ m := Nat.lt_two_pow_self
        have hm2 : 2 ^ m ≤ 2 ^ (m + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega
    _ ≤ 2 ^ (m + 2) * ((3 * 2 ^ (m + 1) - 1) * (3 * 2 ^ (m + 2) - 1)) :=
        Nat.le_mul_of_pos_right _ hpos

end Brockian.AmicableNumbers

