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
# Amicable Infinitude
Category: Brockian Conjecture
Target: Brockian.AmicableNumbers.AmicableInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.AmicableNumbers

open Finset

/-- The sum-of-divisors function `σ₁`. -/
def sigmaOne (n : ℕ) : ℕ := ∑ d ∈ n.divisors, d

/-- Two natural numbers form an *amicable pair* when they are distinct and each is the sum of
the proper divisors of the other; equivalently `σ₁ m = σ₁ n = m + n`. -/
def IsAmicablePair (m n : ℕ) : Prop :=
  m ≠ n ∧ sigmaOne m = m + n ∧ sigmaOne n = m + n

lemma sigmaOne_mul_of_coprime {m n : ℕ} (h : Nat.Coprime m n) :
    sigmaOne (m * n) = sigmaOne m * sigmaOne n :=
  h.sum_divisors_mul

lemma sigmaOne_two_pow (k : ℕ) : sigmaOne (2 ^ k) = 2 ^ (k + 1) - 1 := by
  unfold sigmaOne
  rw [Nat.sum_divisors_prime_pow Nat.prime_two]
  simp [Nat.geomSum_eq]

lemma sigmaOne_prime {p : ℕ} (hp : p.Prime) : sigmaOne p = p + 1 := by
  unfold sigmaOne
  rw [hp.divisors]
  rw [Finset.sum_pair hp.one_lt.ne]
  omega

/-- **Thabit ibn Qurra's rule** (in the arithmetic-free form): if `p + 1 = 3·2^k`,
`q + 1 = 3·2^(k+1)` and `r + 1 = 9·2^(2k+1)` with `p, q, r` prime and `k ≥ 1`, then
`2^(k+1) * (p * q)` and `2^(k+1) * r` form an amicable pair. -/
theorem isAmicablePair_thabit {k p q r : ℕ} (hk : 1 ≤ k)
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hp1 : p + 1 = 3 * 2 ^ k) (hq1 : q + 1 = 3 * 2 ^ (k + 1))
    (hr1 : r + 1 = 9 * 2 ^ (2 * k + 1)) :
    IsAmicablePair (2 ^ (k + 1) * (p * q)) (2 ^ (k + 1) * r) := by
  -- abbreviation `a = 2 ^ k`
  set a : ℕ := 2 ^ k with ha
  have ha2 : 2 ≤ a := by
    calc (2:ℕ) = 2 ^ 1 := by norm_num
    _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  have hpow1 : (2:ℕ) ^ (k + 1) = 2 * a := by rw [ha, pow_succ]; ring
  have hpow2 : (2:ℕ) ^ (k + 1 + 1) = 4 * a := by rw [ha, pow_succ, pow_succ]; ring
  have hq1' : q + 1 = 6 * a := by rw [hq1, hpow1]; ring
  have hr1' : r + 1 = 18 * a ^ 2 := by
    rw [hr1, ha, two_mul, pow_succ, pow_add]; ring
  -- basic primality facts
  have hp2 : p ≠ 2 := by omega
  have hq2 : q ≠ 2 := by omega
  have hr2 : r ≠ 2 := by nlinarith
  have hpq : p ≠ q := by omega
  have hcop2p : Nat.Coprime 2 p := (Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm hp2)
  have hcop2q : Nat.Coprime 2 q := (Nat.coprime_primes Nat.prime_two hq).mpr (Ne.symm hq2)
  have hcop2r : Nat.Coprime 2 r := (Nat.coprime_primes Nat.prime_two hr).mpr (Ne.symm hr2)
  have hcoppq : Nat.Coprime p q := (Nat.coprime_primes hp hq).mpr hpq
  have hc1 : Nat.Coprime (2 ^ (k + 1)) (p * q) :=
    Nat.Coprime.pow_left _ (Nat.Coprime.mul_right hcop2p hcop2q)
  have hc2 : Nat.Coprime (2 ^ (k + 1)) r := Nat.Coprime.pow_left _ hcop2r
  -- the two sigma values
  have hsm : sigmaOne (2 ^ (k + 1) * (p * q)) = (4 * a - 1) * (3 * a) * (6 * a) := by
    rw [sigmaOne_mul_of_coprime hc1, sigmaOne_mul_of_coprime hcoppq, sigmaOne_two_pow,
      sigmaOne_prime hp, sigmaOne_prime hq, hp1, hq1', hpow2]
    ring
  have hsn : sigmaOne (2 ^ (k + 1) * r) = (4 * a - 1) * (18 * a ^ 2) := by
    rw [sigmaOne_mul_of_coprime hc2, sigmaOne_two_pow, sigmaOne_prime hr, hr1', hpow2]
  -- the integer versions of the defining equations
  have haZ : (2:ℤ) ≤ (a : ℤ) := by exact_mod_cast ha2
  have hpZ : (p : ℤ) = 3 * (a : ℤ) - 1 := by
    have : (p : ℤ) + 1 = 3 * (a : ℤ) := by exact_mod_cast hp1
    linarith
  have hqZ : (q : ℤ) = 6 * (a : ℤ) - 1 := by
    have : (q : ℤ) + 1 = 6 * (a : ℤ) := by exact_mod_cast hq1'
    linarith
  have hrZ : (r : ℤ) = 18 * (a : ℤ) ^ 2 - 1 := by
    have : (r : ℤ) + 1 = 18 * (a : ℤ) ^ 2 := by exact_mod_cast hr1'
    linarith
  refine ⟨?_, ?_, ?_⟩
  · -- distinctness
    rw [hpow1]
    intro h
    have h' : p * q = r := by
      have h2 : 0 < 2 * a := by omega
      exact Nat.eq_of_mul_eq_mul_left h2 h
    have h'' : (p : ℤ) * q = r := by exact_mod_cast h'
    rw [hpZ, hqZ, hrZ] at h''
    nlinarith
  · rw [hsm, hpow1]
    zify [show 1 ≤ 4 * a by omega]
    rw [hpZ, hqZ, hrZ]
    ring
  · rw [hsn, hpow1]
    zify [show 1 ≤ 4 * a by omega]
    rw [hpZ, hqZ, hrZ]
    ring

/-- The classical smallest amicable pair, obtained from Thabit's rule with `k = 1`. -/
theorem isAmicablePair_220_284 : IsAmicablePair 220 284 := by
  have := isAmicablePair_thabit (k := 1) (p := 5) (q := 11) (r := 71) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num at this
  exact this

/-- **Conditional infinitude of amicable numbers.**
If there are infinitely many `k` for which the three Thabit numbers `3·2^k - 1`, `3·2^(k+1) - 1`
and `9·2^(2k+1) - 1` are all prime, then there are infinitely many amicable pairs: for every `N`
there is an amicable pair `(m, n)` with `m > N`. -/
theorem AmicableInfinitude
    (H : ∀ N : ℕ, ∃ k, N ≤ k ∧ Nat.Prime (3 * 2 ^ k - 1) ∧ Nat.Prime (3 * 2 ^ (k + 1) - 1) ∧
      Nat.Prime (9 * 2 ^ (2 * k + 1) - 1)) :
    ∀ N : ℕ, ∃ m n : ℕ, N < m ∧ IsAmicablePair m n := by
  intro N
  obtain ⟨k, hk, hp, hq, hr⟩ := H (N + 1)
  have hk1 : 1 ≤ k := le_trans (Nat.le_add_left 1 N) hk
  have h2k : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  have h2k1 : 1 ≤ 2 ^ (k + 1) := Nat.one_le_two_pow
  have h2k2 : 1 ≤ 2 ^ (2 * k + 1) := Nat.one_le_two_pow
  refine ⟨2 ^ (k + 1) * ((3 * 2 ^ k - 1) * (3 * 2 ^ (k + 1) - 1)),
    2 ^ (k + 1) * (9 * 2 ^ (2 * k + 1) - 1), ?_, ?_⟩
  · have hdb : (2:ℕ) ^ (k + 1) = 2 * 2 ^ k := by ring
    have h1 : N < 2 ^ (k + 1) := by
      have hlt : k < 2 ^ k := Nat.lt_two_pow_self
      omega
    have h2 : 1 ≤ (3 * 2 ^ k - 1) * (3 * 2 ^ (k + 1) - 1) :=
      Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
    calc N < 2 ^ (k + 1) := h1
    _ = 2 ^ (k + 1) * 1 := by ring
    _ ≤ _ := Nat.mul_le_mul_left _ h2
  · refine isAmicablePair_thabit hk1 hp hq hr ?_ ?_ ?_ <;>
      exact Nat.sub_add_cancel (by omega)

/-- Reformulation of `AmicableInfinitude`: under the same Thabit-prime hypothesis, the set of
amicable numbers is infinite. -/
theorem infinite_setOf_amicable
    (H : ∀ N : ℕ, ∃ k, N ≤ k ∧ Nat.Prime (3 * 2 ^ k - 1) ∧ Nat.Prime (3 * 2 ^ (k + 1) - 1) ∧
      Nat.Prime (9 * 2 ^ (2 * k + 1) - 1)) :
    {m : ℕ | ∃ n, IsAmicablePair m n}.Infinite := by
  refine Set.infinite_of_forall_exists_gt fun N => ?_
  obtain ⟨m, n, hN, hmn⟩ := AmicableInfinitude H N
  exact ⟨m, ⟨n, hmn⟩, hN⟩

end Brockian.AmicableNumbers

section AxiomCheck
#print axioms Brockian.AmicableNumbers.AmicableInfinitude
#print axioms Brockian.AmicableNumbers.isAmicablePair_220_284
#print axioms Brockian.AmicableNumbers.infinite_setOf_amicable
end AxiomCheck

