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

Whether there are infinitely many amicable numbers is a well-known open problem.
This file gives a Lean-checked **conditional reduction**: if there are infinitely many
Thābit-type exponents `k` (i.e. `3·2^k - 1`, `3·2^(k+1) - 1` and `9·2^(2k+1) - 1` are all
prime), then there are infinitely many amicable numbers.  It also records the
unconditional partial result that amicable numbers exist (the pair `(220, 284)`).
-/

namespace Brockian.AmicableNumbers

open ArithmeticFunction

/-- The sum of the proper divisors of `n`. -/
def properDivisorSum (n : ℕ) : ℕ := ∑ d ∈ n.properDivisors, d

/-- `m` and `n` form an amicable pair: they are distinct and each is the sum of the proper
divisors of the other. -/
def IsAmicablePair (m n : ℕ) : Prop :=
  m ≠ n ∧ properDivisorSum m = n ∧ properDivisorSum n = m

/-- `m` is an amicable number: it belongs to some amicable pair. -/
def IsAmicable (m : ℕ) : Prop := ∃ n, IsAmicablePair m n

/-- A criterion for amicability in terms of the divisor-sum function `σ₁`. -/
theorem isAmicablePair_of_sigma {m n : ℕ} (hmn : m ≠ n)
    (h1 : sigma 1 m = m + n) (h2 : sigma 1 n = m + n) : IsAmicablePair m n := by
  have em : properDivisorSum m + m = m + n := by
    rw [← h1, sigma_one_apply, properDivisorSum,
      Nat.sum_divisors_eq_sum_properDivisors_add_self]
  have en : properDivisorSum n + n = m + n := by
    rw [← h2, sigma_one_apply, properDivisorSum,
      Nat.sum_divisors_eq_sum_properDivisors_add_self]
  exact ⟨hmn, by omega, by omega⟩

theorem sigma_one_prime {p : ℕ} (hp : p.Prime) : sigma 1 p = p + 1 := by
  rw [sigma_one_apply, hp.divisors, Finset.sum_pair hp.one_lt.ne, Nat.add_comm]

theorem sigma_one_two_pow (k : ℕ) : sigma 1 (2 ^ k) + 1 = 2 ^ (k + 1) := by
  have h : sigma 1 (2 ^ k) = 2 ^ (k + 1) - 1 := by
    simp [sigma_one_apply, Nat.sum_divisors_prime_pow Nat.prime_two, Nat.geomSum_eq]
  have h2 : 1 ≤ 2 ^ (k + 1) := Nat.one_le_two_pow
  omega

/-- **Thābit ibn Qurra's rule.**  If `p + 1 = 3·2^k`, `q + 1 = 3·2^(k+1)` and
`r + 1 = 9·2^(2k+1)` are all prime (`k ≥ 1`), then `2^(k+1)·p·q` and `2^(k+1)·r`
form an amicable pair. -/
theorem isAmicablePair_thabit {k p q r : ℕ} (hk : 1 ≤ k) (hp : p.Prime) (hq : q.Prime)
    (hr : r.Prime) (hp1 : p + 1 = 3 * 2 ^ k) (hq1 : q + 1 = 3 * 2 ^ (k + 1))
    (hr1 : r + 1 = 9 * 2 ^ (2 * k + 1)) :
    IsAmicablePair (2 ^ (k + 1) * (p * q)) (2 ^ (k + 1) * r) := by
  have hu : 2 ≤ 2 ^ k := by
    calc (2:ℕ) = 2 ^ 1 := (pow_one 2).symm
    _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  -- basic size facts
  have hp5 : 5 ≤ p := by omega
  have hq5 : 5 ≤ q := by
    have : 3 * 2 ^ k ≤ 3 * 2 ^ (k + 1) :=
      Nat.mul_le_mul_left 3 (Nat.pow_le_pow_right (by norm_num) (by omega))
    omega
  have hr5 : 5 ≤ r := by
    have : (2:ℕ) ≤ 2 ^ (2 * k + 1) := by
      calc (2:ℕ) = 2 ^ 1 := (pow_one 2).symm
      _ ≤ 2 ^ (2 * k + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hpq : p ≠ q := by
    have : 3 * 2 ^ k < 3 * 2 ^ (k + 1) := by
      have : (2:ℕ) ^ k < 2 ^ (k + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
      omega
    omega
  -- oddness
  have hp2 : p ≠ 2 := by omega
  have hq2 : q ≠ 2 := by omega
  have hr2 : r ≠ 2 := by omega
  have cop2 : ∀ {x : ℕ}, x.Prime → x ≠ 2 → Nat.Coprime 2 x := by
    intro x hx hx2
    exact (Nat.coprime_primes Nat.prime_two hx).mpr (fun h => hx2 h.symm)
  have copq : Nat.Coprime p q := (Nat.coprime_primes hp hq).mpr hpq
  have cop2pq : Nat.Coprime (2 ^ (k + 1)) (p * q) :=
    Nat.Coprime.pow_left _ (Nat.Coprime.mul_right (cop2 hp hp2) (cop2 hq hq2))
  have cop2r : Nat.Coprime (2 ^ (k + 1)) r := Nat.Coprime.pow_left _ (cop2 hr hr2)
  -- the divisor sums
  set T := sigma 1 (2 ^ (k + 1)) with hTdef
  have hT : T + 1 = 4 * 2 ^ k := by
    have h1 := sigma_one_two_pow (k + 1)
    have h4 : (2:ℕ) ^ (k + 1 + 1) = 4 * 2 ^ k := by ring
    omega
  have hsM : sigma 1 (2 ^ (k + 1) * (p * q)) = T * ((p + 1) * (q + 1)) := by
    rw [hTdef, isMultiplicative_sigma.map_mul_of_coprime cop2pq,
      isMultiplicative_sigma.map_mul_of_coprime copq, sigma_one_prime hp, sigma_one_prime hq]
  have hsN : sigma 1 (2 ^ (k + 1) * r) = T * (r + 1) := by
    rw [hTdef, isMultiplicative_sigma.map_mul_of_coprime cop2r, sigma_one_prime hr]
  -- the key arithmetic identity
  have hkey : T * (r + 1) = 2 ^ (k + 1) * (p * q) + 2 ^ (k + 1) * r := by
    have hp' : (p : ℤ) = 3 * 2 ^ k - 1 := by
      have h := hp1; zify at h; linarith
    have hq' : (q : ℤ) = 6 * 2 ^ k - 1 := by
      have h := hq1; zify at h; rw [pow_succ] at h; linarith
    have hr' : (r : ℤ) = 18 * (2 ^ k) ^ 2 - 1 := by
      have h := hr1; zify at h
      have hpow : ((2:ℤ)) ^ (2 * k + 1) = 2 * (2 ^ k) ^ 2 := by rw [pow_succ, mul_comm 2 k, pow_mul]; ring
      rw [hpow] at h; linarith
    have hT' : (T : ℤ) = 4 * 2 ^ k - 1 := by
      have h := hT; zify at h; linarith
    have hpow1 : ((2:ℤ)) ^ (k + 1) = 2 * 2 ^ k := by rw [pow_succ]; ring
    zify
    rw [hp', hq', hr', hT', hpow1]
    ring
  have hMq : (p + 1) * (q + 1) = r + 1 := by
    have hpow : (2:ℕ) ^ (2 * k + 1) = 2 * (2 ^ k) ^ 2 := by rw [pow_succ, mul_comm 2 k, pow_mul]; ring
    rw [hp1, hq1, hr1, hpow, pow_succ]; ring
  refine isAmicablePair_of_sigma ?_ ?_ ?_
  · intro h
    have h2 : p * q = r := by
      have hpos : 0 < (2:ℕ) ^ (k + 1) := by positivity
      exact Nat.eq_of_mul_eq_mul_left hpos h
    have h3 : p * q + p + q + 1 = r + 1 := by rw [← hMq]; ring
    omega
  · rw [hsM, hMq]; exact hkey
  · rw [hsN]; exact hkey

/-- A Thābit exponent: `k ≥ 1` such that the three Thābit numbers at `k` are prime. -/
def ThabitExponent (k : ℕ) : Prop :=
  1 ≤ k ∧ ∃ p q r : ℕ, p.Prime ∧ q.Prime ∧ r.Prime ∧
    p + 1 = 3 * 2 ^ k ∧ q + 1 = 3 * 2 ^ (k + 1) ∧ r + 1 = 9 * 2 ^ (2 * k + 1)

/-- **Conditional infinitude of amicable numbers.**  If there are infinitely many Thābit
exponents, then there are infinitely many amicable numbers. -/
theorem AmicableInfinitude (H : {k : ℕ | ThabitExponent k}.Infinite) :
    {m : ℕ | IsAmicable m}.Infinite := by
  apply Set.infinite_of_not_bddAbove
  rintro ⟨N, hN⟩
  obtain ⟨k, hk, hkN⟩ := H.exists_gt N
  obtain ⟨hk1, p, q, r, hp, hq, hr, hp1, hq1, hr1⟩ := hk
  have hpair := isAmicablePair_thabit hk1 hp hq hr hp1 hq1 hr1
  have hmem : (2 ^ (k + 1) * r) ∈ {m : ℕ | IsAmicable m} :=
    ⟨2 ^ (k + 1) * (p * q), fun h => hpair.1 h.symm, hpair.2.2, hpair.2.1⟩
  have hle : 2 ^ (k + 1) * r ≤ N := hN hmem
  have h1 : k < 2 ^ (k + 1) :=
    lt_of_lt_of_le Nat.lt_two_pow_self (Nat.pow_le_pow_right (by norm_num) (by omega))
  have h2 : 1 ≤ r := hr.one_lt.le.trans' (by norm_num)
  have h3 : 2 ^ (k + 1) ≤ 2 ^ (k + 1) * r := Nat.le_mul_of_pos_right _ (by omega)
  omega

/-- Unconditionally, amicable numbers exist: `(220, 284)` is an amicable pair. -/
theorem isAmicablePair_220_284 : IsAmicablePair 220 284 := by
  refine ⟨by norm_num, ?_, ?_⟩ <;> · unfold properDivisorSum; decide

theorem isAmicable_220 : IsAmicable 220 := ⟨284, isAmicablePair_220_284⟩

/-- Thābit's rule is non-vacuous: at `k = 1` it produces the pair `(220, 284)`. -/
theorem isAmicablePair_thabit_one : IsAmicablePair 220 284 := by
  have h := isAmicablePair_thabit (k := 1) (p := 5) (q := 11) (r := 71) le_rfl
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num at h
  exact h

end Brockian.AmicableNumbers

