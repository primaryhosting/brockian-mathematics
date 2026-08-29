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
-- (The header above is a plain block comment rather than a module docstring `/-!`,
-- because Lean 4 requires `import` commands to precede any module docstring.)

import Mathlib
import Archive.Wiedijk100Theorems.PerfectNumbers

/-!
The unconditional statement "there are infinitely many Mersenne primes" is a famous open
problem, so what is proved here is a Lean-checked *reduction*: the set of Mersenne prime
exponents is infinite **iff** the set of even perfect numbers is infinite.  The reduction
goes through the Euclid–Euler correspondence.
-/

namespace Brockian.MersennePerfect

/-- The set of exponents `p` for which `mersenne p = 2 ^ p - 1` is prime. -/
def MersenneExponents : Set ℕ := {p | (mersenne p).Prime}

/-- The set of even perfect numbers. -/
def EvenPerfects : Set ℕ := {n | Even n ∧ Nat.Perfect n}

/-- Euclid's map, sending an exponent `p` to the number `2 ^ (p - 1) * (2 ^ p - 1)`. -/
def euclidPerfect (p : ℕ) : ℕ := 2 ^ (p - 1) * mersenne p

lemma two_le_of_mem_mersenneExponents {p : ℕ} (hp : p ∈ MersenneExponents) : 2 ≤ p :=
  (Nat.Prime.of_mersenne hp).two_le

lemma euclidPerfect_mem_evenPerfects {p : ℕ} (hp : p ∈ MersenneExponents) :
    euclidPerfect p ∈ EvenPerfects := by
  obtain ⟨k, rfl⟩ : ∃ k, p = k + 1 :=
    ⟨p - 1, by have := two_le_of_mem_mersenneExponents hp; omega⟩
  have hpr : (mersenne (k + 1)).Prime := hp
  refine ⟨?_, ?_⟩
  · simpa [euclidPerfect] using Theorems100.Nat.even_two_pow_mul_mersenne_of_prime k hpr
  · simpa [euclidPerfect] using Theorems100.Nat.perfect_two_pow_mul_mersenne_of_prime k hpr

lemma euclidPerfect_strictMonoOn :
    StrictMonoOn euclidPerfect {p : ℕ | 1 ≤ p} := by
  intro a ha b _ hab
  have ha1 : 1 ≤ a := ha
  have h1 : (2:ℕ) ^ (a - 1) ≤ 2 ^ (b - 1) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  have h2 : mersenne a < mersenne b := mersenne_lt_mersenne.2 hab
  exact Nat.mul_lt_mul_of_le_of_lt h1 h2 (Nat.pow_pos (by norm_num))

lemma euclidPerfect_injOn : Set.InjOn euclidPerfect MersenneExponents := by
  intro a ha b hb hab
  have ha1 : a ∈ {p : ℕ | 1 ≤ p} := by
    have := two_le_of_mem_mersenneExponents ha
    simp only [Set.mem_setOf_eq]; omega
  have hb1 : b ∈ {p : ℕ | 1 ≤ p} := by
    have := two_le_of_mem_mersenneExponents hb
    simp only [Set.mem_setOf_eq]; omega
  exact euclidPerfect_strictMonoOn.injOn ha1 hb1 hab

lemma evenPerfects_subset_image :
    EvenPerfects ⊆ euclidPerfect '' MersenneExponents := by
  rintro n ⟨hev, hperf⟩
  obtain ⟨k, hpr, rfl⟩ :=
    Theorems100.Nat.eq_two_pow_mul_prime_mersenne_of_even_perfect hev hperf
  exact ⟨k + 1, hpr, by simp [euclidPerfect]⟩

lemma image_subset_evenPerfects :
    euclidPerfect '' MersenneExponents ⊆ EvenPerfects := by
  rintro n ⟨p, hp, rfl⟩
  exact euclidPerfect_mem_evenPerfects hp

/-- **Mersenne prime infinitude, reduced to even perfect numbers.**
There are infinitely many Mersenne primes (equivalently, infinitely many exponents `p` with
`2 ^ p - 1` prime) if and only if there are infinitely many even perfect numbers.
Both implications go through the Euclid–Euler correspondence `p ↦ 2 ^ (p - 1) * (2 ^ p - 1)`. -/
theorem MersennePrimeInfinitude :
    MersenneExponents.Infinite ↔ EvenPerfects.Infinite := by
  constructor
  · intro h
    exact (h.image euclidPerfect_injOn).mono image_subset_evenPerfects
  · intro h
    by_contra hfin
    rw [Set.not_infinite] at hfin
    exact h ((hfin.image euclidPerfect).subset evenPerfects_subset_image)

/-! ### The set of Mersenne primes itself -/

/-- The set of Mersenne primes, i.e. primes of the form `2 ^ p - 1`. -/
def MersennePrimes : Set ℕ := {q | q.Prime ∧ ∃ p, q = mersenne p}

lemma mersennePrimes_eq_image : MersennePrimes = mersenne '' MersenneExponents := by
  ext q
  constructor
  · rintro ⟨hq, p, rfl⟩
    exact ⟨p, hq, rfl⟩
  · rintro ⟨p, hp, rfl⟩
    exact ⟨hp, p, rfl⟩

/-- The set of Mersenne primes is infinite iff the set of their exponents is. -/
theorem mersennePrimes_infinite_iff :
    MersennePrimes.Infinite ↔ MersenneExponents.Infinite := by
  rw [mersennePrimes_eq_image]
  exact Set.infinite_image_iff strictMono_mersenne.injective.injOn

/-- **Reduction, phrased for the Mersenne primes themselves.** -/
theorem mersennePrimes_infinite_iff_evenPerfects_infinite :
    MersennePrimes.Infinite ↔ EvenPerfects.Infinite :=
  mersennePrimes_infinite_iff.trans MersennePrimeInfinitude

/-! ### Unboundedness reformulation -/

/-- Infinitely many Mersenne primes is the same as: arbitrarily large exponents work. -/
theorem mersenneExponents_infinite_iff_unbounded :
    MersenneExponents.Infinite ↔ ∀ N : ℕ, ∃ p, N < p ∧ (mersenne p).Prime := by
  constructor
  · intro h N
    obtain ⟨p, hp, hlt⟩ := h.exists_gt N
    exact ⟨p, hlt, hp⟩
  · intro h
    exact Set.infinite_of_forall_exists_gt fun N => by
      obtain ⟨p, hlt, hp⟩ := h N
      exact ⟨p, hp, hlt⟩

/-! ### Unconditional facts and examples -/

/-- The exponent of a Mersenne prime is itself prime. -/
theorem prime_of_mem_mersenneExponents {p : ℕ} (hp : p ∈ MersenneExponents) : p.Prime :=
  Nat.Prime.of_mersenne hp

example : (3 : ℕ) ∈ MersennePrimes := ⟨by norm_num, 2, by decide⟩

example : (7 : ℕ) ∈ MersennePrimes := ⟨by norm_num, 3, by decide⟩

example : (31 : ℕ) ∈ MersennePrimes := ⟨by norm_num, 5, by decide⟩

example : (127 : ℕ) ∈ MersennePrimes := ⟨by norm_num, 7, by decide⟩

/-- The first four even perfect numbers, obtained from the first four Mersenne primes. -/
example : ({6, 28, 496, 8128} : Set ℕ) ⊆ EvenPerfects := by
  have h : ∀ p : ℕ, p ∈ MersenneExponents → euclidPerfect p ∈ EvenPerfects := fun _ h =>
    euclidPerfect_mem_evenPerfects h
  rintro n (rfl | rfl | rfl | rfl)
  · simpa [euclidPerfect, mersenne] using h 2 (by norm_num [MersenneExponents, mersenne])
  · simpa [euclidPerfect, mersenne] using h 3 (by norm_num [MersenneExponents, mersenne])
  · simpa [euclidPerfect, mersenne] using h 5 (by norm_num [MersenneExponents, mersenne])
  · simpa [euclidPerfect, mersenne] using h 7 (by norm_num [MersenneExponents, mersenne])

end Brockian.MersennePerfect

