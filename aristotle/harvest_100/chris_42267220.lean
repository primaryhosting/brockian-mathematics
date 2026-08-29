import Brockian.MersennePerfect

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
# Even Perfect Infinitude
Category: Brockian Conjecture
Target: Brockian.MersennePerfect.EvenPerfectInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(Note: written as a plain block comment rather than a module docstring, since Lean 4
requires `import` commands to precede any module docstring.)
-/

import Mathlib

namespace Brockian.MersennePerfect

open Finset

/-- The set of exponents `p` for which the Mersenne number `2 ^ p - 1` is prime. -/
def MersennePrimeExponents : Set ℕ := {p : ℕ | (mersenne p).Prime}

/-- The set of even perfect numbers. -/
def EvenPerfects : Set ℕ := {n : ℕ | Even n ∧ n.Perfect}

/-- Sum of a geometric series of powers of two. -/
lemma sum_range_two_pow (k : ℕ) : ∑ x ∈ range (k + 1), 2 ^ x = 2 ^ (k + 1) - 1 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, ih]
    have h : 1 ≤ 2 ^ (k + 1) := Nat.one_le_two_pow
    have : 2 ^ (k + 2) = 2 ^ (k + 1) + 2 ^ (k + 1) := by ring
    omega

/-- The Mersenne number `2 ^ (k+1) - 1` is odd. -/
lemma mersenne_succ_odd (k : ℕ) : Odd (mersenne (k + 1)) := by
  have h : 1 ≤ 2 ^ (k + 1) := Nat.one_le_two_pow
  have h2 : (2 : ℕ) ∣ 2 ^ (k + 1) := dvd_pow_self 2 (Nat.succ_ne_zero k)
  obtain ⟨c, hc⟩ := h2
  refine ⟨c - 1, ?_⟩
  simp only [mersenne]
  omega

/-- **Euclid's theorem on perfect numbers**: if `2 ^ (k+1) - 1` is prime, then
`2 ^ k * (2 ^ (k+1) - 1)` is a perfect number. -/
theorem perfect_two_pow_mul_mersenne {k : ℕ} (h : (mersenne (k + 1)).Prime) :
    Nat.Perfect (2 ^ k * mersenne (k + 1)) := by
  set q := mersenne (k + 1) with hq
  have hqpos : 0 < q := h.pos
  have hpos : 0 < 2 ^ k * q := Nat.mul_pos (Nat.two_pow_pos k) hqpos
  have hcop : Nat.Coprime (2 ^ k) q :=
    Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr (mersenne_succ_odd k))
  rw [Nat.perfect_iff_sum_divisors_eq_two_mul hpos]
  have hsum : ∑ i ∈ (2 ^ k * q).divisors, i
      = (∑ i ∈ (2 ^ k : ℕ).divisors, i) * (∑ i ∈ q.divisors, i) := by
    have := (ArithmeticFunction.isMultiplicative_sigma (k := 1)).map_mul_of_coprime hcop
    simpa [ArithmeticFunction.sigma_one_apply] using this
  have h1 : ∑ i ∈ (2 ^ k : ℕ).divisors, i = 2 ^ (k + 1) - 1 := by
    rw [Nat.sum_divisors_prime_pow Nat.prime_two, sum_range_two_pow]
  have h2 : ∑ i ∈ q.divisors, i = q + 1 := by
    rw [h.divisors]
    rw [Finset.sum_pair h.one_lt.ne]
    omega
  have hq1 : q + 1 = 2 ^ (k + 1) := by
    have : 1 ≤ 2 ^ (k + 1) := Nat.one_le_two_pow
    simp only [hq, mersenne]
    omega
  rw [hsum, h1, h2, hq1]
  have hqval : q = 2 ^ (k + 1) - 1 := rfl
  have hle : 1 ≤ 2 ^ (k + 1) := Nat.one_le_two_pow
  have : 2 ^ (k + 1) = 2 * 2 ^ k := by ring
  rw [hqval]
  cases Nat.exists_eq_add_of_le hle with
  | intro c hc =>
    rw [this] at hc ⊢
    nlinarith [hc]

/-- If the Mersenne prime exponent `p` is at least `1`, the associated Euclid number
`2 ^ (p-1) * (2 ^ p - 1)` is even. -/
lemma even_euclid_number {p : ℕ} (hp : 1 ≤ p) (h : (mersenne p).Prime) :
    Even (2 ^ (p - 1) * mersenne p) := by
  obtain ⟨k, rfl⟩ : ∃ k, p = k + 2 := by
    rcases p with _ | _ | k
    · omega
    · exfalso
      simp [mersenne] at h
      exact Nat.not_prime_one h
    · exact ⟨k, rfl⟩
  exact Even.mul_right (by simp [Nat.even_pow]) _

/-- Euclid numbers built from Mersenne primes are even perfect numbers. -/
lemma euclid_number_mem_evenPerfects {p : ℕ} (hp : 1 ≤ p) (h : p ∈ MersennePrimeExponents) :
    2 ^ (p - 1) * mersenne p ∈ EvenPerfects := by
  refine ⟨even_euclid_number hp h, ?_⟩
  obtain ⟨k, rfl⟩ : ∃ k, p = k + 1 := ⟨p - 1, by omega⟩
  simpa using perfect_two_pow_mul_mersenne (k := k) h

/-- **Conditional reduction (Euclid direction).** If there are infinitely many Mersenne primes,
then there are infinitely many even perfect numbers. -/
theorem EvenPerfectInfinitude (h : MersennePrimeExponents.Infinite) : EvenPerfects.Infinite := by
  refine Set.infinite_of_forall_exists_gt fun N => ?_
  obtain ⟨p, hp, hpN⟩ := h.exists_gt (N + 1)
  have hp1 : 1 ≤ p := by omega
  refine ⟨2 ^ (p - 1) * mersenne p, euclid_number_mem_evenPerfects hp1 hp, ?_⟩
  have hm : 1 ≤ mersenne p := by
    have := (hp : (mersenne p).Prime)
    exact this.one_lt.le.trans' (by omega)
  have hpow : p - 1 < 2 ^ (p - 1) := Nat.lt_two_pow_self
  calc N < p - 1 := by omega
    _ < 2 ^ (p - 1) := hpow
    _ ≤ 2 ^ (p - 1) * mersenne p := Nat.le_mul_of_pos_right _ (by omega)

/-- The divisor sum of `2 ^ k * m` for odd `m`. -/
lemma sum_divisors_two_pow_mul_odd (k : ℕ) {m : ℕ} (hm : Odd m) :
    ∑ i ∈ (2 ^ k * m).divisors, i = (2 ^ (k + 1) - 1) * ∑ i ∈ m.divisors, i := by
  have hcop : Nat.Coprime (2 ^ k) m :=
    Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hm)
  have hmul : ∑ i ∈ (2 ^ k * m).divisors, i
      = (∑ i ∈ (2 ^ k : ℕ).divisors, i) * (∑ i ∈ m.divisors, i) := by
    have := (ArithmeticFunction.isMultiplicative_sigma (k := 1)).map_mul_of_coprime hcop
    simpa [ArithmeticFunction.sigma_one_apply] using this
  rw [hmul, Nat.sum_divisors_prime_pow Nat.prime_two, sum_range_two_pow]

/-- **Euler's theorem on even perfect numbers**: every even perfect number has the form
`2 ^ k * (2 ^ (k+1) - 1)` with `2 ^ (k+1) - 1` prime. -/
theorem even_perfect_eq_two_pow_mul_mersenne {n : ℕ} (hn : Even n) (hp : n.Perfect) :
    ∃ k, (mersenne (k + 1)).Prime ∧ n = 2 ^ k * mersenne (k + 1) := by
  have hn0 : 0 < n := hp.2
  obtain ⟨k, m, hm, rfl⟩ := Nat.exists_eq_two_pow_mul_odd hn0.ne'
  have hm0 : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · simp [h] at hn0
    · exact h
  have hk : 1 ≤ k := by
    by_contra hk
    have hk0 : k = 0 := by omega
    subst hk0
    simp only [pow_zero, one_mul] at hn
    exact (Nat.not_even_iff_odd.mpr hm) hn
  set q := mersenne (k + 1) with hqdef
  have hqval : q = 2 ^ (k + 1) - 1 := rfl
  have hpow : 4 ≤ 2 ^ (k + 1) := by
    calc (4 : ℕ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (k + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hq3 : 3 ≤ q := by rw [hqval]; omega
  have hq1 : q + 1 = 2 ^ (k + 1) := by rw [hqval]; omega
  set S := ∑ i ∈ m.divisors, i with hS
  have hkey : q * S = 2 ^ (k + 1) * m := by
    have h2 := (Nat.perfect_iff_sum_divisors_eq_two_mul hn0).1 hp
    rw [sum_divisors_two_pow_mul_odd k hm] at h2
    rw [hqval, hS]
    rw [h2]
    ring
  have hqodd : Odd q := mersenne_succ_odd k
  have hcop : Nat.Coprime q (2 ^ (k + 1)) :=
    Nat.Coprime.pow_right _ (Nat.coprime_two_right.mpr hqodd)
  have hqdvd : q ∣ m := by
    refine hcop.dvd_of_dvd_mul_left ?_
    exact ⟨S, hkey.symm⟩
  obtain ⟨j, hj⟩ := hqdvd
  have hj0 : 0 < j := by
    rcases Nat.eq_zero_or_pos j with h | h
    · simp [h] at hj; omega
    · exact h
  have hSval : S = m + j := by
    have hq0 : 0 < q := by omega
    have : q * S = q * (m + j) := by
      rw [hkey, hj]
      calc 2 ^ (k + 1) * (q * j) = (q + 1) * (q * j) := by rw [hq1]
        _ = q * (q * j + j) := by ring
    exact Nat.eq_of_mul_eq_mul_left hq0 this
  have hprop : ∑ i ∈ m.properDivisors, i = j := by
    have := Nat.sum_divisors_eq_sum_properDivisors_add_self (n := m)
    rw [← hS, hSval] at this
    omega
  have hjm : j < m := by
    rw [hj]
    nlinarith
  have hjdvd : j ∣ m := ⟨q, by rw [hj]; ring⟩
  have hm1 : 1 < m := by rw [hj]; nlinarith
  have hjone : j = 1 := by
    by_contra hne
    have h1mem : (1 : ℕ) ∈ m.properDivisors := Nat.one_mem_properDivisors_iff_one_lt.mpr hm1
    have hjmem : j ∈ m.properDivisors := Nat.mem_properDivisors.mpr ⟨hjdvd, hjm⟩
    have hsub : ({1, j} : Finset ℕ) ⊆ m.properDivisors := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact h1mem
      · exact hjmem
    have hle : ∑ i ∈ ({1, j} : Finset ℕ), i ≤ ∑ i ∈ m.properDivisors, i :=
      Finset.sum_le_sum_of_subset hsub
    rw [Finset.sum_pair (Ne.symm hne), hprop] at hle
    omega
  subst hjone
  refine ⟨k, ?_, ?_⟩
  · have hmq : m = q := by omega
    rw [← hqdef, ← hmq]
    exact Nat.sum_properDivisors_eq_one_iff_prime.mp (by rw [hprop])
  · congr 1
    omega

/-- If there are infinitely many even perfect numbers, there are infinitely many
Mersenne primes. -/
theorem mersenne_infinite_of_evenPerfects_infinite (h : EvenPerfects.Infinite) :
    MersennePrimeExponents.Infinite := by
  refine Set.infinite_of_forall_exists_gt fun N => ?_
  obtain ⟨n, hn, hnN⟩ := h.exists_gt (2 ^ (2 * N + 2))
  obtain ⟨k, hkp, rfl⟩ := even_perfect_eq_two_pow_mul_mersenne hn.1 hn.2
  refine ⟨k + 1, hkp, ?_⟩
  by_contra hcon
  have hkN : k + 1 ≤ N := by omega
  have hub : 2 ^ k * mersenne (k + 1) < 2 ^ (2 * k + 1) := by
    have h1 : mersenne (k + 1) < 2 ^ (k + 1) := by
      simp only [mersenne]
      have : 1 ≤ 2 ^ (k + 1) := Nat.one_le_two_pow
      omega
    calc 2 ^ k * mersenne (k + 1) < 2 ^ k * 2 ^ (k + 1) := by gcongr
      _ = 2 ^ (2 * k + 1) := by rw [← pow_add]; ring_nf
  have hmono : (2 : ℕ) ^ (2 * k + 1) ≤ 2 ^ (2 * N + 2) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

/-- Sanity checks: `6` and `28` are even perfect numbers. -/
example : 6 ∈ EvenPerfects :=
  ⟨by decide, by rw [Nat.perfect_iff_sum_properDivisors (by norm_num)]; decide⟩

example : 28 ∈ EvenPerfects :=
  ⟨by decide, by rw [Nat.perfect_iff_sum_properDivisors (by norm_num)]; decide⟩

example : 2 ∈ MersennePrimeExponents := by
  show (mersenne 2).Prime
  norm_num [mersenne]

/-- **Euclid–Euler reduction.** There are infinitely many even perfect numbers if and only if
there are infinitely many Mersenne primes. -/
theorem evenPerfects_infinite_iff : EvenPerfects.Infinite ↔ MersennePrimeExponents.Infinite :=
  ⟨mersenne_infinite_of_evenPerfects_infinite, EvenPerfectInfinitude⟩

end Brockian.MersennePerfect

