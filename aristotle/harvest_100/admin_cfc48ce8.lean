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
/-!
# Even Perfect Infinitude
Category: Brockian Conjecture
Target: Brockian.MersennePerfect.EvenPerfectInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (The header above is wrapped in an outer block comment because Lean 4 requires
-- `import` commands to precede every other command, including module docstrings.)
-/

import Mathlib
import Archive.Wiedijk100Theorems.PerfectNumbers

/-!
Whether there are infinitely many even perfect numbers is an open problem (it is equivalent
to the infinitude of Mersenne primes).  What is proved here is exactly that equivalence, i.e.
a Lean-checked reduction of the conjecture:

  `{n | Even n ∧ n.Perfect}.Infinite ↔ {p | (mersenne p).Prime}.Infinite`

The proof goes through the Euclid–Euler theorem: the map `p ↦ 2 ^ (p - 1) * (2 ^ p - 1)`
is a bijection from the set of Mersenne exponents `p` with `2 ^ p - 1` prime onto the set of
even perfect numbers.
-/

namespace Brockian.MersennePerfect

open Set

/-- The set of exponents `p` for which `mersenne p = 2 ^ p - 1` is prime. -/
def mersenneExponents : Set ℕ := {p : ℕ | (mersenne p).Prime}

/-- The set of even perfect numbers. -/
def evenPerfects : Set ℕ := {n : ℕ | Even n ∧ n.Perfect}

/-- Euclid's map, sending a Mersenne exponent `p` to `2 ^ (p - 1) * (2 ^ p - 1)`. -/
def euclidMap (p : ℕ) : ℕ := 2 ^ (p - 1) * mersenne p

/-- A Mersenne exponent is positive: `mersenne 0 = 0` is not prime. -/
theorem one_le_of_mem_mersenneExponents {p : ℕ} (hp : p ∈ mersenneExponents) : 1 ≤ p := by
  rcases Nat.eq_zero_or_pos p with rfl | h
  · simp [mersenneExponents, mersenne, Nat.not_prime_zero] at hp
  · exact h

/-- `euclidMap` is strictly increasing on positive exponents. -/
theorem euclidMap_lt_euclidMap {a b : ℕ} (ha : 1 ≤ a) (hab : a < b) :
    euclidMap a < euclidMap b := by
  have h1 : (2 : ℕ) ^ (a - 1) ≤ 2 ^ (b - 1) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  have h2 : mersenne a < mersenne b := by
    have : (2 : ℕ) ^ a < 2 ^ b := Nat.pow_lt_pow_right (by norm_num) hab
    have h2a : 1 ≤ (2 : ℕ) ^ a := Nat.one_le_two_pow
    simp only [mersenne]
    omega
  have hpos : 0 < (2 : ℕ) ^ (b - 1) := Nat.two_pow_pos _
  exact Nat.mul_lt_mul_of_le_of_lt h1 h2 hpos

/-- `euclidMap` is injective on the set of Mersenne exponents. -/
theorem injOn_euclidMap : InjOn euclidMap mersenneExponents := by
  intro a ha b hb hab
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · exact absurd hab (euclidMap_lt_euclidMap (one_le_of_mem_mersenneExponents ha) h).ne
  · exact absurd hab.symm (euclidMap_lt_euclidMap (one_le_of_mem_mersenneExponents hb) h).ne

/-- **Euclid's direction**: Euclid's map sends Mersenne exponents to even perfect numbers. -/
theorem euclidMap_mem_evenPerfects {p : ℕ} (hp : p ∈ mersenneExponents) :
    euclidMap p ∈ evenPerfects := by
  obtain ⟨k, rfl⟩ : ∃ k, p = k + 1 :=
    ⟨p - 1, by have := one_le_of_mem_mersenneExponents hp; omega⟩
  have hpr : (mersenne (k + 1)).Prime := hp
  refine ⟨?_, ?_⟩
  · simpa [euclidMap] using Theorems100.Nat.even_two_pow_mul_mersenne_of_prime k hpr
  · simpa [euclidMap] using Theorems100.Nat.perfect_two_pow_mul_mersenne_of_prime k hpr

/-- **Euler's direction**: every even perfect number is the image of a Mersenne exponent. -/
theorem exists_mersenneExponent_of_mem_evenPerfects {n : ℕ} (hn : n ∈ evenPerfects) :
    ∃ p ∈ mersenneExponents, euclidMap p = n := by
  obtain ⟨k, hpr, rfl⟩ :=
    Theorems100.Nat.eq_two_pow_mul_prime_mersenne_of_even_perfect hn.1 hn.2
  exact ⟨k + 1, hpr, by simp [euclidMap]⟩

/-- The Euclid–Euler correspondence: the even perfect numbers are exactly the images of the
Mersenne exponents under `p ↦ 2 ^ (p - 1) * (2 ^ p - 1)`. -/
theorem image_euclidMap_mersenneExponents : euclidMap '' mersenneExponents = evenPerfects := by
  apply Set.Subset.antisymm
  · rintro _ ⟨p, hp, rfl⟩
    exact euclidMap_mem_evenPerfects hp
  · intro n hn
    obtain ⟨p, hp, hpn⟩ := exists_mersenneExponent_of_mem_evenPerfects hn
    exact ⟨p, hp, hpn⟩

/-- **Even Perfect Infinitude (conditional reduction).**
There are infinitely many even perfect numbers if and only if there are infinitely many
Mersenne primes, i.e. infinitely many exponents `p` with `2 ^ p - 1` prime. -/
theorem EvenPerfectInfinitude :
    {n : ℕ | Even n ∧ n.Perfect}.Infinite ↔ {p : ℕ | (mersenne p).Prime}.Infinite := by
  show evenPerfects.Infinite ↔ mersenneExponents.Infinite
  rw [← image_euclidMap_mersenneExponents, Set.infinite_image_iff injOn_euclidMap]

/-- Forward form of the reduction: infinitely many Mersenne primes gives infinitely many
even perfect numbers. -/
theorem infinite_evenPerfect_of_infinite_mersennePrime
    (h : {p : ℕ | (mersenne p).Prime}.Infinite) : {n : ℕ | Even n ∧ n.Perfect}.Infinite :=
  EvenPerfectInfinitude.2 h

/-- Backward form of the reduction: infinitely many even perfect numbers gives infinitely many
Mersenne primes. -/
theorem infinite_mersennePrime_of_infinite_evenPerfect
    (h : {n : ℕ | Even n ∧ n.Perfect}.Infinite) : {p : ℕ | (mersenne p).Prime}.Infinite :=
  EvenPerfectInfinitude.1 h

/-- Sanity check that the statement is not vacuous: `6` is an even perfect number. -/
theorem six_mem_evenPerfects : 6 ∈ evenPerfects := by
  have h : (2 : ℕ) ∈ mersenneExponents := by
    show (mersenne 2).Prime
    norm_num [mersenne]
  simpa [euclidMap, mersenne] using euclidMap_mem_evenPerfects h

#print axioms EvenPerfectInfinitude

end Brockian.MersennePerfect

