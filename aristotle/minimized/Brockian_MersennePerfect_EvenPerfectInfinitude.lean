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

(Note: Lean 4 does not permit a module doc-comment before the import lines, so the
required header appears here as an ordinary block comment; the same text is repeated
as the module docstring immediately after the imports.)
-/

import Mathlib
import Archive.Wiedijk100Theorems.PerfectNumbers

/-!
# Even Perfect Infinitude
Category: Brockian Conjecture
Target: Brockian.MersennePerfect.EvenPerfectInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

The statement "there are infinitely many even perfect numbers" is open, since it is
equivalent to the (open) conjecture that there are infinitely many Mersenne primes.

What is proved here is exactly that equivalence: a Lean-checked *conditional reduction*
of the infinitude of even perfect numbers to the infinitude of Mersenne primes.

The key input is the Euclid–Euler theorem, already available in Mathlib's Archive as
`Theorems100.Nat.even_and_perfect_iff`
(`Archive/Wiedijk100Theorems/PerfectNumbers.lean`), which states
`Even n ∧ n.Perfect ↔ ∃ k, (mersenne (k + 1)).Prime ∧ n = 2 ^ k * mersenne (k + 1)`.
-/

namespace Brockian
namespace MersennePerfect

open Nat

/-- The set of even perfect numbers. -/

def evenPerfects : Set ℕ := {n : ℕ | Even n ∧ Nat.Perfect n}

/-- The set of exponents `k` such that `mersenne (k + 1) = 2 ^ (k + 1) - 1` is prime. -/

def mersenneExponents : Set ℕ := {k : ℕ | Nat.Prime (mersenne (k + 1))}

/-- The Euclid map sending a Mersenne exponent `k` to the perfect number
`2 ^ k * (2 ^ (k + 1) - 1)`. -/

def euclid (k : ℕ) : ℕ := 2 ^ k * mersenne (k + 1)

lemma euclid_strictMono : StrictMono euclid := by
  apply strictMono_nat_of_lt_succ
  intro k
  have h1 : (2 : ℕ) ^ k < 2 ^ (k + 1) := by
    exact Nat.pow_lt_pow_right (by norm_num) (Nat.lt_succ_self k)
  have h2 : mersenne (k + 1) ≤ mersenne (k + 2) := by
    simp only [mersenne]
    have : (2 : ℕ) ^ (k + 1) ≤ 2 ^ (k + 2) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have h3 : 0 < mersenne (k + 1) := by
    simp only [mersenne]
    have : (2 : ℕ) ^ 1 ≤ 2 ^ (k + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  calc euclid k = 2 ^ k * mersenne (k + 1) := rfl
    _ < 2 ^ (k + 1) * mersenne (k + 1) := by
        exact Nat.mul_lt_mul_of_lt_of_le h1 (le_refl _) h3
    _ ≤ 2 ^ (k + 1) * mersenne (k + 2) := by
        exact Nat.mul_le_mul_left _ h2
    _ = euclid (k + 1) := rfl

lemma euclid_injective : Function.Injective euclid := euclid_strictMono.injective

/-- Euclid's direction: the image of a Mersenne exponent is an even perfect number. -/

lemma euclid_mem_evenPerfects {k : ℕ} (hk : k ∈ mersenneExponents) :
    euclid k ∈ evenPerfects :=
  Theorems100.Nat.even_and_perfect_iff.mpr ⟨k, hk, rfl⟩

/-- Euler's direction: every even perfect number is in the image of `euclid`. -/

lemma evenPerfects_subset_image : evenPerfects ⊆ euclid '' mersenneExponents := by
  intro n hn
  obtain ⟨k, hk, rfl⟩ := Theorems100.Nat.even_and_perfect_iff.mp hn
  exact ⟨k, hk, rfl⟩

lemma image_subset_evenPerfects : euclid '' mersenneExponents ⊆ evenPerfects := by
  rintro _ ⟨k, hk, rfl⟩
  exact euclid_mem_evenPerfects hk

/-- The set of even perfect numbers is exactly the Euclid image of the set of
Mersenne exponents. -/

theorem evenPerfects_eq_image : evenPerfects = euclid '' mersenneExponents :=
  Set.Subset.antisymm evenPerfects_subset_image image_subset_evenPerfects

/--
**Even Perfect Infinitude (conditional reduction).**

There are infinitely many even perfect numbers if and only if there are infinitely many
Mersenne primes, i.e. infinitely many `k` with `2 ^ (k + 1) - 1` prime.

Both sides are open problems; the content of the theorem is the equivalence, which is the
Euclid–Euler theorem together with injectivity of `k ↦ 2 ^ k * (2 ^ (k + 1) - 1)`.
-/

theorem EvenPerfectInfinitude :
    {n : ℕ | Even n ∧ Nat.Perfect n}.Infinite ↔
      {k : ℕ | Nat.Prime (mersenne (k + 1))}.Infinite := by
  have h : ({n : ℕ | Even n ∧ Nat.Perfect n} : Set ℕ) = euclid '' mersenneExponents :=
    evenPerfects_eq_image
  rw [h]
  exact Set.infinite_image_iff (euclid_injective.injOn)

/-- Consequently, if there are infinitely many Mersenne primes then there are infinitely
many even perfect numbers. -/
