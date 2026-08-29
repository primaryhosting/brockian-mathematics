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

/-- The sum of the proper divisors of `n` (all divisors of `n` other than `n` itself). -/
def s (n : ℕ) : ℕ := ∑ d ∈ n.properDivisors, d

/-- `a` and `b` form an amicable pair: they are distinct and each is the sum of the
proper divisors of the other. -/
def IsAmicablePair (a b : ℕ) : Prop := a ≠ b ∧ s a = b ∧ s b = a

/-- `n` is an amicable number if it belongs to some amicable pair. -/
def IsAmicable (n : ℕ) : Prop := ∃ m, IsAmicablePair n m

/-- The set of amicable numbers. -/
def amicableSet : Set ℕ := {n | IsAmicable n}

/-! ## A concrete amicable pair -/

theorem isAmicablePair_220_284 : IsAmicablePair 220 284 := by
  refine ⟨by decide, ?_, ?_⟩ <;> · unfold s; decide

theorem isAmicable_220 : IsAmicable 220 := ⟨284, isAmicablePair_220_284⟩

set_option maxRecDepth 100000 in
theorem isAmicablePair_1184_1210 : IsAmicablePair 1184 1210 := by
  refine ⟨by decide, ?_, ?_⟩ <;> · unfold s; decide

/-- Being an amicable pair is a symmetric relation. -/
theorem IsAmicablePair.symm {a b : ℕ} (h : IsAmicablePair a b) : IsAmicablePair b a :=
  ⟨h.1.symm, h.2.2, h.2.1⟩

/-- The set of amicable numbers is infinite exactly when it is unbounded. -/
theorem amicableSet_infinite_iff :
    amicableSet.Infinite ↔ ∀ N : ℕ, ∃ n ∈ amicableSet, N < n := by
  constructor
  · intro hinf N
    obtain ⟨n, hn, hn'⟩ := hinf.exists_gt N
    exact ⟨n, hn, hn'⟩
  · exact Set.infinite_of_forall_exists_gt

/-! ## Sum-of-divisors preliminaries -/

/-- `σ₁ n`, the sum of all divisors of `n`. -/
def sigma1 (n : ℕ) : ℕ := ∑ d ∈ n.divisors, d

theorem sigma1_eq_s_add_self (n : ℕ) : sigma1 n = s n + n :=
  Nat.sum_divisors_eq_sum_properDivisors_add_self

theorem sigma1_eq_sigma (n : ℕ) : sigma1 n = ArithmeticFunction.sigma 1 n := by
  rw [ArithmeticFunction.sigma_one_apply, sigma1]

theorem sigma1_mul_of_coprime {m n : ℕ} (h : Nat.Coprime m n) :
    sigma1 (m * n) = sigma1 m * sigma1 n := by
  simp only [sigma1_eq_sigma]
  exact ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime h

theorem geom_two (m : ℕ) : ∑ i ∈ Finset.range (m + 1), 2 ^ i + 1 = 2 ^ (m + 1) := by
  induction m with
  | zero => decide
  | succ n ih => rw [Finset.sum_range_succ]; ring_nf; ring_nf at ih; omega

theorem sigma1_two_pow (m : ℕ) : sigma1 (2 ^ m) + 1 = 2 ^ (m + 1) := by
  have h : sigma1 (2 ^ m) = ∑ i ∈ Finset.range (m + 1), 2 ^ i := by
    unfold sigma1
    exact Nat.sum_divisors_prime_pow Nat.prime_two
  rw [h, geom_two]

theorem sigma1_prime {p : ℕ} (hp : p.Prime) : sigma1 p = p + 1 := by
  unfold sigma1
  rw [hp.sum_divisors]

/-! ## Thabit ibn Qurra's rule -/

/-- The Thabit condition at `k ≥ 1`: the three numbers `3·2^k - 1`, `3·2^(k+1) - 1` and
`9·2^(2k+1) - 1` are all prime. -/
def ThabitTriple (k : ℕ) : Prop :=
  1 ≤ k ∧ Nat.Prime (3 * 2 ^ k - 1) ∧ Nat.Prime (3 * 2 ^ (k + 1) - 1) ∧
    Nat.Prime (9 * 2 ^ (2 * k + 1) - 1)

/-- Thabit ibn Qurra's rule: if `p = 3·2^k - 1`, `q = 3·2^(k+1) - 1` and `r = 9·2^(2k+1) - 1`
are all prime (with `k ≥ 1`), then `2^(k+1)·p·q` and `2^(k+1)·r` form an amicable pair. -/
theorem thabit_rule {k : ℕ} (h : ThabitTriple k) :
    IsAmicablePair (2 ^ (k + 1) * ((3 * 2 ^ k - 1) * (3 * 2 ^ (k + 1) - 1)))
      (2 ^ (k + 1) * (9 * 2 ^ (2 * k + 1) - 1)) := by
  obtain ⟨hk, hp, hq, hr⟩ := h
  set p := 3 * 2 ^ k - 1 with hpdef
  set q := 3 * 2 ^ (k + 1) - 1 with hqdef
  set r := 9 * 2 ^ (2 * k + 1) - 1 with hrdef
  have hx : 2 ≤ 2 ^ k := by
    calc (2:ℕ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  have hp1 : p + 1 = 3 * 2 ^ k := by omega
  have hq1 : q + 1 = 3 * 2 ^ (k + 1) := by
    have : 2 ≤ 2 ^ (k + 1) := le_trans hx (Nat.pow_le_pow_right (by norm_num) (by omega))
    omega
  have hr1 : r + 1 = 9 * 2 ^ (2 * k + 1) := by
    have : 2 ≤ 2 ^ (2 * k + 1) := le_trans hx (Nat.pow_le_pow_right (by norm_num) (by omega))
    omega
  obtain ⟨t, ht⟩ : (2:ℕ) ∣ 2 ^ k := dvd_pow_self 2 (by omega)
  have hodd_p : ¬ (2 ∣ p) := by omega
  have hodd_q : ¬ (2 ∣ q) := by
    have h2 : (2:ℕ) ∣ 2 ^ (k + 1) := dvd_pow_self 2 (by omega)
    obtain ⟨u, hu⟩ := h2
    omega
  have hodd_r : ¬ (2 ∣ r) := by
    have h2 : (2:ℕ) ∣ 2 ^ (2 * k + 1) := dvd_pow_self 2 (by omega)
    obtain ⟨u, hu⟩ := h2
    omega
  have cp : Nat.Coprime 2 p := (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hodd_p
  have cq : Nat.Coprime 2 q := (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hodd_q
  have cr : Nat.Coprime 2 r := (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hodd_r
  have hpq_ne : p ≠ q := by
    have : 3 * 2 ^ k < 3 * 2 ^ (k + 1) := by
      have : (2:ℕ) ^ k < 2 ^ (k + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
      omega
    omega
  have cpq : Nat.Coprime p q := (Nat.coprime_primes hp hq).mpr hpq_ne
  have ca : Nat.Coprime (2 ^ (k + 1)) (p * q) := Nat.Coprime.pow_left _ (Nat.Coprime.mul_right cp cq)
  have cb : Nat.Coprime (2 ^ (k + 1)) r := Nat.Coprime.pow_left _ cr
  have hsa : sigma1 (2 ^ (k + 1) * (p * q)) = sigma1 (2 ^ (k + 1)) * ((p + 1) * (q + 1)) := by
    rw [sigma1_mul_of_coprime ca, sigma1_mul_of_coprime cpq, sigma1_prime hp, sigma1_prime hq]
  have hsb : sigma1 (2 ^ (k + 1) * r) = sigma1 (2 ^ (k + 1)) * (r + 1) := by
    rw [sigma1_mul_of_coprime cb, sigma1_prime hr]
  have hT : sigma1 (2 ^ (k + 1)) + 1 = 2 ^ (k + 2) := sigma1_two_pow (k + 1)
  set T := sigma1 (2 ^ (k + 1)) with hTdef
  -- integer versions of all the relations
  set A : ℤ := (2 : ℤ) ^ k with hA
  have hA2 : (2:ℤ) ≤ A := by rw [hA]; exact_mod_cast hx
  have hpI : (p : ℤ) = 3 * A - 1 := by
    have h3 := congrArg (Nat.cast (R := ℤ)) hp1
    push_cast at h3
    rw [← hA] at h3
    linarith
  have hqI : (q : ℤ) = 6 * A - 1 := by
    have e : ((2:ℤ)) ^ (k + 1) = 2 * A := by rw [hA]; ring
    have h6 := congrArg (Nat.cast (R := ℤ)) hq1
    push_cast at h6
    rw [e] at h6
    linarith
  have hrI : (r : ℤ) = 18 * A ^ 2 - 1 := by
    have e : ((2:ℤ)) ^ (2 * k + 1) = 2 * A ^ 2 := by rw [hA]; ring
    have h9 := congrArg (Nat.cast (R := ℤ)) hr1
    push_cast at h9
    rw [e] at h9
    linarith
  have hTI : (T : ℤ) = 4 * A - 1 := by
    have e : ((2:ℤ)) ^ (k + 2) = 4 * A := by rw [hA]; ring
    have h4 := congrArg (Nat.cast (R := ℤ)) hT
    push_cast at h4
    rw [e] at h4
    linarith
  have hab : (2:ℕ) ^ (k + 1) * (p * q) < 2 ^ (k + 1) * r := by
    have hlt : (p : ℤ) * q < (r : ℤ) := by rw [hpI, hqI, hrI]; nlinarith [hA2]
    have : p * q < r := by exact_mod_cast hlt
    exact mul_lt_mul_of_pos_left this (by positivity)
  have hkey : T * ((p + 1) * (q + 1)) = 2 ^ (k + 1) * (p * q) + 2 ^ (k + 1) * r := by
    have hI : (T : ℤ) * (((p : ℤ) + 1) * ((q : ℤ) + 1))
        = (2 * A) * ((p : ℤ) * q) + (2 * A) * (r : ℤ) := by
      rw [hpI, hqI, hrI, hTI]; ring
    have h2 : ((2:ℕ) ^ (k + 1) : ℤ) = 2 * A := by rw [hA]; push_cast; ring
    have : ((T * ((p + 1) * (q + 1)) : ℕ) : ℤ)
        = ((2 ^ (k + 1) * (p * q) + 2 ^ (k + 1) * r : ℕ) : ℤ) := by
      push_cast
      push_cast at h2
      rw [h2]
      linear_combination hI
    exact_mod_cast this
  have hkey2 : T * (r + 1) = 2 ^ (k + 1) * (p * q) + 2 ^ (k + 1) * r := by
    rw [← hkey]
    have hI : (T : ℤ) * ((r : ℤ) + 1) = (T : ℤ) * (((p : ℤ) + 1) * ((q : ℤ) + 1)) := by
      rw [hpI, hqI, hrI]; ring
    have : ((T * (r + 1) : ℕ) : ℤ) = ((T * ((p + 1) * (q + 1)) : ℕ) : ℤ) := by push_cast; exact hI
    exact_mod_cast this
  refine ⟨Nat.ne_of_lt hab, ?_, ?_⟩
  · have h1 := sigma1_eq_s_add_self (2 ^ (k + 1) * (p * q))
    rw [hsa, hkey] at h1
    omega
  · have h1 := sigma1_eq_s_add_self (2 ^ (k + 1) * r)
    rw [hsb, hkey2] at h1
    omega

/-- Thabit's rule at `k = 1` recovers the classical pair `(220, 284)`. -/
theorem thabit_rule_one : IsAmicablePair 220 284 := by
  have h : ThabitTriple 1 := ⟨le_refl 1, by norm_num, by norm_num, by norm_num⟩
  have := thabit_rule h
  norm_num at this
  exact this

/-! ## The conditional infinitude statement -/

/-- **Conditional infinitude of amicable numbers.**  If Thabit's condition holds for
infinitely many `k` (i.e. for arbitrarily large `k` the three Thabit numbers are all prime),
then there are infinitely many amicable numbers. -/
theorem AmicableInfinitude (h : ∀ N, ∃ k, N < k ∧ ThabitTriple k) : amicableSet.Infinite := by
  apply Set.infinite_of_forall_exists_gt
  intro N
  obtain ⟨k, hkN, hk⟩ := h N
  refine ⟨2 ^ (k + 1) * ((3 * 2 ^ k - 1) * (3 * 2 ^ (k + 1) - 1)), ⟨_, thabit_rule hk⟩, ?_⟩
  obtain ⟨hk1, hp, hq, _⟩ := hk
  have hx : 2 ≤ 2 ^ k := by
    calc (2:ℕ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk1
  have hkk : k < 2 ^ k := Nat.lt_two_pow_self
  have h1 : 1 ≤ (3 * 2 ^ k - 1) * (3 * 2 ^ (k + 1) - 1) := by
    have := hp.two_le
    have := hq.two_le
    nlinarith
  calc N < k := hkN
    _ < 2 ^ k := hkk
    _ ≤ 2 ^ (k + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    _ ≤ 2 ^ (k + 1) * ((3 * 2 ^ k - 1) * (3 * 2 ^ (k + 1) - 1)) := Nat.le_mul_of_pos_right _ h1

end Brockian.AmicableNumbers

