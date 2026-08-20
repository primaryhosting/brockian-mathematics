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

import Archive.Wiedijk100Theorems.PerfectNumbers

/-!
Whether there are infinitely many Mersenne primes is a famous open problem, so we prove a
Lean-checked *conditional reduction*: the set of Mersenne primes is infinite **if and only if**
the set of even perfect numbers is infinite.

The mathematical input is the Euclid–Euler theorem, available in Mathlib's archive as
`Theorems100.Nat.even_and_perfect_iff`.
-/

namespace Brockian
namespace MersennePerfect

open Nat

/-- The set of Mersenne primes: primes of the form `2 ^ k - 1`. -/
def mersennePrimes : Set ℕ := {p : ℕ | p.Prime ∧ ∃ k : ℕ, p = mersenne k}

/-- The set of even perfect numbers. -/
def evenPerfects : Set ℕ := {n : ℕ | Even n ∧ Nat.Perfect n}

/-- Exponents `k` such that `2 ^ (k + 1) - 1` is prime. -/
def mersenneExponents : Set ℕ := {k : ℕ | Nat.Prime (mersenne (k + 1))}

lemma mersenne_strictMono : StrictMono mersenne := by
  intro a b hab
  simpa [mersenne] using
    Nat.sub_lt_sub_right (Nat.one_le_two_pow) (Nat.pow_lt_pow_right one_lt_two hab)

lemma mersenne_succ_injective : Function.Injective fun k : ℕ => mersenne (k + 1) :=
  fun a b h => by
    have := mersenne_strictMono.injective h
    omega

lemma euclidMap_strictMono : StrictMono fun k : ℕ => 2 ^ k * mersenne (k + 1) := by
  apply strictMono_nat_of_lt_succ
  intro k
  have h1 : (2 : ℕ) ^ k < 2 ^ (k + 1) := Nat.pow_lt_pow_right one_lt_two (by omega)
  have h2 : mersenne (k + 1) ≤ mersenne (k + 2) :=
    (mersenne_strictMono (by omega)).le
  have h3 : 0 < mersenne (k + 1) := by
    have : (2 : ℕ) ^ 1 ≤ 2 ^ (k + 1) := Nat.pow_le_pow_right (by omega) (by omega)
    simp only [mersenne]
    omega
  calc 2 ^ k * mersenne (k + 1) < 2 ^ (k + 1) * mersenne (k + 1) :=
        Nat.mul_lt_mul_of_lt_of_le h1 le_rfl h3
    _ ≤ 2 ^ (k + 1) * mersenne (k + 2) := Nat.mul_le_mul_left _ h2

lemma euclidMap_injective : Function.Injective fun k : ℕ => 2 ^ k * mersenne (k + 1) :=
  euclidMap_strictMono.injective

/-- The Mersenne primes are exactly the values `mersenne (k + 1)` for `k` a Mersenne exponent. -/
lemma image_mersenne_succ :
    (fun k : ℕ => mersenne (k + 1)) '' mersenneExponents = mersennePrimes := by
  ext p
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨hk, ⟨k + 1, rfl⟩⟩
  · rintro ⟨hp, j, rfl⟩
    match j with
    | 0 => simp [mersenne, Nat.not_prime_zero] at hp
    | (k + 1) => exact ⟨k, hp, rfl⟩

/-- Euclid–Euler: the even perfect numbers are exactly the numbers `2 ^ k * (2 ^ (k + 1) - 1)`
for `k` a Mersenne exponent. -/
lemma image_euclidMap :
    (fun k : ℕ => 2 ^ k * mersenne (k + 1)) '' mersenneExponents = evenPerfects := by
  ext n
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact Theorems100.Nat.even_and_perfect_iff.2 ⟨k, hk, rfl⟩
  · rintro hn
    obtain ⟨k, hk, rfl⟩ := Theorems100.Nat.even_and_perfect_iff.1 hn
    exact ⟨k, hk, rfl⟩

/-- **Conditional reduction of the Mersenne prime infinitude problem.**

There are infinitely many Mersenne primes if and only if there are infinitely many even
perfect numbers.  (Both statements are open; the equivalence is the Euclid–Euler theorem.) -/
theorem MersennePrimeInfinitude :
    mersennePrimes.Infinite ↔ evenPerfects.Infinite := by
  rw [← image_mersenne_succ, ← image_euclidMap,
    Set.infinite_image_iff (mersenne_succ_injective.injOn),
    Set.infinite_image_iff (euclidMap_injective.injOn)]

/-- Sanity check: the equivalence is not vacuous, e.g. `7` is a Mersenne prime. -/
example : 7 ∈ mersennePrimes := ⟨by norm_num, 3, by norm_num [mersenne]⟩

/-- Sanity check: `28 = 2 ^ 2 * (2 ^ 3 - 1)` is an even perfect number. -/
example : 28 ∈ evenPerfects := by
  have h : Nat.Prime (mersenne (2 + 1)) := by norm_num [mersenne]
  have h2 : (28 : ℕ) = 2 ^ 2 * mersenne (2 + 1) := by norm_num [mersenne]
  show Even (28 : ℕ) ∧ Nat.Perfect 28
  rw [h2]
  exact Theorems100.Nat.even_and_perfect_iff.2 ⟨2, h, rfl⟩

end MersennePerfect
end Brockian

