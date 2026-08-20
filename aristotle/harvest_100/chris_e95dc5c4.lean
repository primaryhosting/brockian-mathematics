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
-/

import Mathlib

/-!
# Even Perfect Infinitude
Category: Brockian Conjecture
Target: Brockian.MersennePerfect.EvenPerfectInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

Whether there are infinitely many even perfect numbers is a famous open problem, equivalent
to the infinitude of Mersenne primes.  What is proved here is exactly that equivalence: the
set of even perfect numbers is infinite **iff** the set of Mersenne primes is infinite.

The mathematical input is the Euclid–Euler theorem.  Mathlib contains it in the
`Archive` (see `Archive/Wiedijk100Theorems/PerfectNumbers.lean`, Theorem 70 of the
100 Theorems list, by Aaron Anderson), but the `Archive` is not importable from a
downstream project, so the relevant statements are reproved here, following that file.
-/

namespace Brockian

namespace MersennePerfect

open ArithmeticFunction Finset

open scoped sigma

/-- `σ 1 (2 ^ k) = 2 ^ (k+1) - 1`. -/
theorem sigma_two_pow_eq_mersenne_succ (k : ℕ) : σ 1 (2 ^ k) = mersenne (k + 1) := by
  simp_rw [sigma_one_apply, mersenne, ← one_add_one_eq_two, ← geom_sum_mul_add 1 (k + 1)]
  norm_num

/-- Euclid's theorem that Mersenne primes induce perfect numbers. -/
theorem perfect_two_pow_mul_mersenne_of_prime (k : ℕ) (pr : (mersenne (k + 1)).Prime) :
    Nat.Perfect (2 ^ k * mersenne (k + 1)) := by
  rw [Nat.perfect_iff_sum_divisors_eq_two_mul, ← mul_assoc, ← pow_succ', ← sigma_one_apply,
    mul_comm,
    isMultiplicative_sigma.map_mul_of_coprime ((Odd.coprime_two_right (by simp)).pow_right _),
    sigma_two_pow_eq_mersenne_succ]
  · simp [pr, sigma_one_apply]
  · positivity

theorem ne_zero_of_prime_mersenne (k : ℕ) (pr : (mersenne (k + 1)).Prime) : k ≠ 0 := by
  intro H
  simp [H, mersenne, Nat.not_prime_one] at pr

theorem even_two_pow_mul_mersenne_of_prime (k : ℕ) (pr : (mersenne (k + 1)).Prime) :
    Even (2 ^ k * mersenne (k + 1)) := by
  simp [ne_zero_of_prime_mersenne k pr, parity_simps]

theorem eq_two_pow_mul_odd {n : ℕ} (hpos : 0 < n) : ∃ k m : ℕ, n = 2 ^ k * m ∧ ¬Even m := by
  have h := Nat.finiteMultiplicity_iff.2 ⟨Nat.prime_two.ne_one, hpos⟩
  obtain ⟨m, hm⟩ := pow_multiplicity_dvd 2 n
  use multiplicity 2 n, m
  refine ⟨hm, ?_⟩
  rw [even_iff_two_dvd]
  have hg := h.not_pow_dvd_of_multiplicity_lt (Nat.lt_succ_self _)
  contrapose! hg
  rcases hg with ⟨k, rfl⟩
  apply Dvd.intro k
  rw [pow_succ, mul_assoc, ← hm]

/-- **Perfect Number Theorem** (Euler): even perfect numbers factor as a power of two times a
Mersenne prime. -/
theorem eq_two_pow_mul_prime_mersenne_of_even_perfect {n : ℕ} (ev : Even n)
    (perf : Nat.Perfect n) :
    ∃ k : ℕ, Nat.Prime (mersenne (k + 1)) ∧ n = 2 ^ k * mersenne (k + 1) := by
  have hpos := perf.2
  rcases eq_two_pow_mul_odd hpos with ⟨k, m, rfl, hm⟩
  use k
  rw [even_iff_two_dvd] at hm
  rw [Nat.perfect_iff_sum_divisors_eq_two_mul hpos, ← sigma_one_apply,
    isMultiplicative_sigma.map_mul_of_coprime (Nat.prime_two.coprime_pow_of_not_dvd hm).symm,
    sigma_two_pow_eq_mersenne_succ, ← mul_assoc, ← pow_succ'] at perf
  obtain ⟨j, rfl⟩ := ((Odd.coprime_two_right (by simp)).pow_right _).dvd_of_dvd_mul_left
    (Dvd.intro _ perf)
  rw [← mul_assoc, mul_comm _ (mersenne _), mul_assoc] at perf
  have h := mul_left_cancel₀ (by positivity) perf
  rw [sigma_one_apply, Nat.sum_divisors_eq_sum_properDivisors_add_self, ← succ_mersenne, add_mul,
    one_mul, add_comm] at h
  have hj := add_left_cancel h
  cases Nat.sum_properDivisors_dvd (by rw [hj]; apply Dvd.intro_left (mersenne (k + 1)) rfl) with
  | inl h_1 =>
    have j1 : j = 1 := Eq.trans hj.symm h_1
    rw [j1, mul_one, Nat.sum_properDivisors_eq_one_iff_prime] at h_1
    simp [h_1, j1]
  | inr h_1 =>
    have jcon := Eq.trans hj.symm h_1
    rw [← one_mul j, ← mul_assoc, mul_one] at jcon
    have jcon2 := mul_right_cancel₀ ?_ jcon
    · exfalso
      match k with
      | 0 =>
        apply hm
        rw [← jcon2, pow_zero, one_mul, one_mul] at ev
        rw [← jcon2, one_mul]
        exact even_iff_two_dvd.mp ev
      | .succ k =>
        apply ne_of_lt _ jcon2
        rw [mersenne, ← Nat.pred_eq_sub_one, Nat.lt_pred_iff, ← pow_one (Nat.succ 1)]
        apply pow_lt_pow_right₀ (Nat.lt_succ_self 1) (Nat.succ_lt_succ k.succ_pos)
    contrapose! hm
    simp [hm]

/-- The Euclid–Euler theorem characterizing even perfect numbers. -/
theorem even_and_perfect_iff {n : ℕ} :
    Even n ∧ Nat.Perfect n ↔ ∃ k : ℕ, Nat.Prime (mersenne (k + 1)) ∧
      n = 2 ^ k * mersenne (k + 1) := by
  constructor
  · rintro ⟨ev, perf⟩
    exact eq_two_pow_mul_prime_mersenne_of_even_perfect ev perf
  · rintro ⟨k, pr, rfl⟩
    exact ⟨even_two_pow_mul_mersenne_of_prime k pr, perfect_two_pow_mul_mersenne_of_prime k pr⟩

/-- The Euclid–Euler map `k ↦ 2 ^ k * (2 ^ (k+1) - 1)`. -/
def euclidEuler (k : ℕ) : ℕ := 2 ^ k * mersenne (k + 1)

theorem euclidEuler_strictMono : StrictMono euclidEuler := by
  apply strictMono_nat_of_lt_succ
  intro k
  have h1 : (2 : ℕ) ^ k < 2 ^ (k + 1) :=
    Nat.pow_lt_pow_right (by norm_num) (Nat.lt_succ_self k)
  have h2 : mersenne (k + 1) < mersenne (k + 2) := by
    have h5 : (2 : ℕ) ^ (k + 1) < 2 ^ (k + 2) :=
      Nat.pow_lt_pow_right (by norm_num) (Nat.lt_succ_self _)
    have h3 : 1 ≤ (2 : ℕ) ^ (k + 1) := Nat.one_le_two_pow
    simp only [mersenne]
    omega
  have h4 : 0 < mersenne (k + 1) := by
    have : 1 < (2 : ℕ) ^ (k + 1) := Nat.one_lt_two_pow (by omega)
    simp only [mersenne]; omega
  simpa [euclidEuler] using Nat.mul_lt_mul_of_lt_of_lt h1 h2

theorem euclidEuler_injective : Function.Injective euclidEuler :=
  euclidEuler_strictMono.injective

/-- The set of even perfect numbers is exactly the image, under the Euclid–Euler map, of the
set of exponents giving Mersenne primes. -/
theorem evenPerfect_eq_image :
    {n : ℕ | Even n ∧ Nat.Perfect n} = euclidEuler '' {k : ℕ | Nat.Prime (mersenne (k + 1))} := by
  ext n
  simp only [Set.mem_setOf_eq, Set.mem_image, euclidEuler]
  rw [even_and_perfect_iff]
  constructor
  · rintro ⟨k, pr, rfl⟩; exact ⟨k, pr, rfl⟩
  · rintro ⟨k, pr, rfl⟩; exact ⟨k, pr, rfl⟩

/-- **Even Perfect Infinitude (reduction).**  There are infinitely many even perfect numbers
if and only if there are infinitely many Mersenne primes, i.e. infinitely many exponents `k`
with `2 ^ (k+1) - 1` prime. -/
theorem EvenPerfectInfinitude :
    {n : ℕ | Even n ∧ Nat.Perfect n}.Infinite ↔
      {k : ℕ | Nat.Prime (mersenne (k + 1))}.Infinite := by
  rw [evenPerfect_eq_image]
  exact ⟨fun h => h.of_image _, fun h => h.image euclidEuler_injective.injOn⟩

/-- Unbounded form of the reduction: if there are infinitely many Mersenne primes, then for
every `N` there is an even perfect number exceeding `N`. -/
theorem exists_gt_even_perfect_of_infinite_mersenne
    (h : {k : ℕ | Nat.Prime (mersenne (k + 1))}.Infinite) (N : ℕ) :
    ∃ n, N < n ∧ Even n ∧ Nat.Perfect n := by
  obtain ⟨n, hn, hNn⟩ := (EvenPerfectInfinitude.2 h).exists_gt N
  exact ⟨n, hNn, hn⟩

/-- Sanity check: the equivalence is not vacuous — `6 = 2^1 * (2^2 - 1)` is an even perfect
number, coming from the Mersenne prime `3`. -/
theorem even_perfect_six : (6 : ℕ) ∈ {n : ℕ | Even n ∧ Nat.Perfect n} := by
  have h : Nat.Prime (mersenne (1 + 1)) := by decide
  refine even_and_perfect_iff.2 ⟨1, h, ?_⟩
  decide

end MersennePerfect

end Brockian

