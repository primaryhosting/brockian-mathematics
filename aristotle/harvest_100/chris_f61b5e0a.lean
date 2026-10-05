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
import Archive.Wiedijk100Theorems.PerfectNumbers

/-!
The infinitude of even perfect numbers is an open problem: by the Euclid–Euler theorem it is
equivalent to the infinitude of Mersenne primes, which is unknown.  What is proved here is
precisely that equivalence, in the form of a Lean-checked reduction:

* `Brockian.MersennePerfect.EvenPerfectInfinitude` : the set of even perfect numbers is infinite
  **iff** the set of Mersenne prime exponents is infinite.
* `Brockian.MersennePerfect.evenPerfect_infinite_of_mersenne_infinite` : the conditional form
  (infinitely many Mersenne primes ⟹ infinitely many even perfect numbers).
-/

namespace Brockian.MersennePerfect

open Nat

/-- The set of even perfect numbers. -/
def EvenPerfects : Set ℕ := {n | Even n ∧ Nat.Perfect n}

/-- The set of `k` such that the Mersenne number `2 ^ (k + 1) - 1` is prime. -/
def MersenneExponents : Set ℕ := {k | Nat.Prime (mersenne (k + 1))}

/-- The Euclid map `k ↦ 2 ^ k * (2 ^ (k + 1) - 1)`. -/
def euclidMap (k : ℕ) : ℕ := 2 ^ k * mersenne (k + 1)

lemma mersenne_succ_pos (k : ℕ) : 0 < mersenne (k + 1) := by
  have h : (2 : ℕ) ^ 1 ≤ 2 ^ (k + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  simp only [mersenne]
  omega

lemma euclidMap_strictMono : StrictMono euclidMap := by
  apply strictMono_nat_of_lt_succ
  intro n
  have h1 : (2 : ℕ) ^ n ≤ 2 ^ (n + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h2 : mersenne (n + 1) < mersenne (n + 1 + 1) := by
    have hlt : (2 : ℕ) ^ (n + 1) < 2 ^ (n + 1 + 1) :=
      Nat.pow_lt_pow_right (by norm_num) (by omega)
    have hp := mersenne_succ_pos n
    simp only [mersenne] at *
    omega
  have h3 : 2 ^ n * mersenne (n + 1) ≤ 2 ^ (n + 1) * mersenne (n + 1) :=
    Nat.mul_le_mul_right _ h1
  have h4 : 2 ^ (n + 1) * mersenne (n + 1) < 2 ^ (n + 1) * mersenne (n + 1 + 1) :=
    by gcongr
  simpa [euclidMap] using lt_of_le_of_lt h3 h4

lemma euclidMap_injective : Function.Injective euclidMap :=
  euclidMap_strictMono.injective

/-- **Euclid–Euler**, restated as a set identity: the even perfect numbers are exactly the
image of the Mersenne prime exponents under `k ↦ 2 ^ k * (2 ^ (k + 1) - 1)`. -/
theorem evenPerfects_eq_image : EvenPerfects = euclidMap '' MersenneExponents := by
  ext n
  simp only [EvenPerfects, MersenneExponents, Set.mem_setOf_eq, Set.mem_image, euclidMap]
  rw [Theorems100.Nat.even_and_perfect_iff]
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨k, hk, rfl⟩
  · rintro ⟨k, hk, rfl⟩
    exact ⟨k, hk, rfl⟩

/-- **Even Perfect Infinitude (conditional reduction).**  There are infinitely many even perfect
numbers if and only if there are infinitely many Mersenne primes. -/
theorem EvenPerfectInfinitude : EvenPerfects.Infinite ↔ MersenneExponents.Infinite := by
  rw [evenPerfects_eq_image, Set.infinite_image_iff euclidMap_injective.injOn]

/-- The conditional form: infinitely many Mersenne primes yields infinitely many even
perfect numbers. -/
theorem evenPerfect_infinite_of_mersenne_infinite (h : MersenneExponents.Infinite) :
    EvenPerfects.Infinite :=
  EvenPerfectInfinitude.mpr h

/-- Conversely, infinitely many even perfect numbers yields infinitely many Mersenne primes. -/
theorem mersenne_infinite_of_evenPerfect_infinite (h : EvenPerfects.Infinite) :
    MersenneExponents.Infinite :=
  EvenPerfectInfinitude.mp h

/-- A sanity check that the sets involved are non-vacuous: `6` is an even perfect number,
witnessed by the Mersenne prime `3 = 2 ^ 2 - 1`. -/
theorem six_mem_evenPerfects : 6 ∈ EvenPerfects := by
  have hp : Nat.Prime (mersenne (1 + 1)) := by norm_num [mersenne]
  refine ⟨⟨3, by norm_num⟩, ?_⟩
  have := Theorems100.Nat.perfect_two_pow_mul_mersenne_of_prime 1 hp
  norm_num [mersenne] at this
  exact this

#print axioms EvenPerfectInfinitude

end Brockian.MersennePerfect

