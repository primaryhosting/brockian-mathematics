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
# Mersenne Prime Infinitude
Category: Brockian Conjecture
Target: Brockian.MersennePerfect.MersennePrimeInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Mersenne Prime Infinitude
Category: Brockian Conjecture
Target: Brockian.MersennePerfect.MersennePrimeInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

The infinitude of Mersenne primes is a famous open problem, so what is established here is a
*Lean-checked conditional reduction*: the set of Mersenne prime exponents is infinite **iff**
the set of even perfect numbers is infinite.  This is obtained from an explicit, unconditional
bijection (Euclid–Euler): the strictly monotone map `k ↦ 2 ^ (k - 1) * (2 ^ k - 1)` carries the
set of exponents `k` with `2 ^ k - 1` prime *onto* the set of even perfect numbers.

The proof of the Euclid–Euler theorem itself is reproduced here (it lives in the `Archive`
component of Mathlib, which is not importable from this project); the argument follows
`Archive/Wiedijk100Theorems/PerfectNumbers.lean` by Aaron Anderson.
-/

namespace Brockian.MersennePerfect

open ArithmeticFunction Finset
open scoped sigma

/-! ## Euclid–Euler -/

private theorem sigma_two_pow_eq_mersenne_succ (k : ℕ) : σ 1 (2 ^ k) = mersenne (k + 1) := by
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

private theorem ne_zero_of_prime_mersenne (k : ℕ) (pr : (mersenne (k + 1)).Prime) : k ≠ 0 := by
  intro H
  simp [H, mersenne, Nat.not_prime_one] at pr

theorem even_two_pow_mul_mersenne_of_prime (k : ℕ) (pr : (mersenne (k + 1)).Prime) :
    Even (2 ^ k * mersenne (k + 1)) := by
  simp [ne_zero_of_prime_mersenne k pr, parity_simps]

private theorem eq_two_pow_mul_odd {n : ℕ} (hpos : 0 < n) : ∃ k m : ℕ, n = 2 ^ k * m ∧ ¬Even m := by
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

/-- **Euler's theorem**: an even perfect number is a power of two times a Mersenne prime. -/
theorem eq_two_pow_mul_prime_mersenne_of_even_perfect {n : ℕ} (ev : Even n) (perf : Nat.Perfect n) :
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

/-! ## The sets in play -/

/-- The set of exponents `k` for which `mersenne k = 2 ^ k - 1` is prime. -/
def MersenneExponents : Set ℕ := {k : ℕ | (mersenne k).Prime}

/-- The set of even perfect numbers. -/
def EvenPerfects : Set ℕ := {n : ℕ | Even n ∧ n.Perfect}

/-- The Euclid–Euler map `k ↦ 2 ^ (k - 1) * (2 ^ k - 1)`. -/
def euclidEuler (k : ℕ) : ℕ := 2 ^ (k - 1) * mersenne k

theorem strictMono_euclidEuler : StrictMono euclidEuler := by
  refine strictMono_nat_of_lt_succ fun k => ?_
  match k with
  | 0 => decide
  | (j + 1) =>
      have h1 : (2 : ℕ) ^ j < 2 ^ (j + 1) :=
        Nat.pow_lt_pow_right (by norm_num) (Nat.lt_succ_self j)
      have h2 : mersenne (j + 1) < mersenne (j + 1 + 1) := strictMono_mersenne (by omega)
      have h3 : 0 < mersenne (j + 1) := by simp
      have : 2 ^ j * mersenne (j + 1) < 2 ^ (j + 1) * mersenne (j + 1 + 1) :=
        Nat.mul_lt_mul_of_lt_of_le h1 h2.le (by positivity)
      simpa [euclidEuler] using this

theorem euclidEuler_injective : Function.Injective euclidEuler :=
  strictMono_euclidEuler.injective

/-- Every exponent of a Mersenne prime is positive. -/
theorem pos_of_mem_mersenneExponents {k : ℕ} (hk : k ∈ MersenneExponents) : 0 < k := by
  rcases Nat.eq_zero_or_pos k with rfl | h
  · rw [MersenneExponents, Set.mem_setOf_eq, mersenne_zero] at hk
    exact absurd hk Nat.not_prime_zero
  · exact h

/-- Every exponent of a Mersenne prime is itself prime. -/
theorem prime_of_mem_mersenneExponents {k : ℕ} (hk : k ∈ MersenneExponents) : k.Prime :=
  Nat.Prime.of_mersenne hk

/-! ## The Euclid–Euler bijection -/

/-- **Euclid–Euler, set form**: the map `k ↦ 2 ^ (k - 1) * (2 ^ k - 1)` sends the set of
Mersenne prime exponents exactly onto the set of even perfect numbers. -/
theorem image_mersenneExponents_eq_evenPerfects :
    euclidEuler '' MersenneExponents = EvenPerfects := by
  ext n
  constructor
  · rintro ⟨k, hk, rfl⟩
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by have := pos_of_mem_mersenneExponents hk; omega⟩
    have pr : (mersenne (j + 1)).Prime := hk
    refine ⟨?_, ?_⟩
    · simpa [euclidEuler] using even_two_pow_mul_mersenne_of_prime j pr
    · simpa [euclidEuler] using perfect_two_pow_mul_mersenne_of_prime j pr
  · rintro ⟨ev, perf⟩
    obtain ⟨k, pr, hn⟩ := eq_two_pow_mul_prime_mersenne_of_even_perfect ev perf
    exact ⟨k + 1, pr, by simpa [euclidEuler] using hn.symm⟩

/-! ## The main conditional reduction -/

/-- **Mersenne prime infinitude, conditional reduction.**

There are infinitely many Mersenne primes if and only if there are infinitely many even
perfect numbers.  (Both sides are open problems; the content here is the unconditional
Euclid–Euler correspondence, which makes them equivalent.) -/
theorem MersennePrimeInfinitude :
    MersenneExponents.Infinite ↔ EvenPerfects.Infinite := by
  constructor
  · intro h
    rw [← image_mersenneExponents_eq_evenPerfects]
    exact h.image euclidEuler_injective.injOn
  · intro h
    rw [← image_mersenneExponents_eq_evenPerfects] at h
    exact h.of_image _

/-- Equivalently: there are infinitely many Mersenne primes iff there are arbitrarily large
even perfect numbers. -/
theorem mersenneExponents_infinite_iff_evenPerfect_unbounded :
    MersenneExponents.Infinite ↔ ∀ N : ℕ, ∃ n > N, Even n ∧ n.Perfect := by
  rw [MersennePrimeInfinitude]
  constructor
  · intro h N
    obtain ⟨n, hn, hN⟩ := h.exists_gt N
    exact ⟨n, hN, hn.1, hn.2⟩
  · intro h
    apply Set.infinite_of_not_bddAbove
    rintro ⟨N, hN⟩
    obtain ⟨n, hn, hev, hp⟩ := h N
    exact absurd (hN (show n ∈ EvenPerfects from ⟨hev, hp⟩)) (by omega)

/-! ## Unconditional partial results -/

/-- There are at least five Mersenne primes: the exponents `2, 3, 5, 7, 13` all work. -/
theorem mersenneExponents_examples :
    ({2, 3, 5, 7, 13} : Set ℕ) ⊆ MersenneExponents := by
  rintro k (rfl | rfl | rfl | rfl | rfl) <;>
    · show (mersenne _).Prime
      norm_num [mersenne]

/-- Consequently there are at least five even perfect numbers: `6, 28, 496, 8128, 33550336`. -/
theorem evenPerfects_examples :
    ({6, 28, 496, 8128, 33550336} : Set ℕ) ⊆ EvenPerfects := by
  have h : ∀ k ∈ ({2, 3, 5, 7, 13} : Set ℕ), euclidEuler k ∈ EvenPerfects := by
    intro k hk
    rw [← image_mersenneExponents_eq_evenPerfects]
    exact ⟨k, mersenneExponents_examples hk, rfl⟩
  rintro n (rfl | rfl | rfl | rfl | rfl)
  · simpa [euclidEuler, mersenne] using h 2 (by norm_num)
  · simpa [euclidEuler, mersenne] using h 3 (by norm_num)
  · simpa [euclidEuler, mersenne] using h 5 (by norm_num)
  · simpa [euclidEuler, mersenne] using h 7 (by norm_num)
  · simpa [euclidEuler, mersenne] using h 13 (by norm_num)

end Brockian.MersennePerfect

