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
-- (Lean 4 requires `import` lines to precede any module docstring `/-! ... -/`,
-- so the header above is written as a plain block comment.)

import Archive.Wiedijk100Theorems.PerfectNumbers

/-!
# Mersenne Prime Infinitude

The infinitude of Mersenne primes is a well-known open problem, so what is proved here is a
Lean-checked *reduction*: the set of Mersenne primes is infinite if and only if the set of even
perfect numbers is infinite.  The reduction is powered by the Euclid–Euler theorem, available in
Mathlib's archive as `Theorems100.Nat.even_and_perfect_iff`.
-/

namespace Brockian.MersennePerfect

/-- The set of Mersenne primes, i.e. primes of the form `2 ^ k - 1`. -/

def mersennePrimes : Set ℕ := {p | p.Prime ∧ ∃ k, p = mersenne k}

/-- The set of even perfect numbers. -/

def evenPerfects : Set ℕ := {n | Even n ∧ n.Perfect}

/-- The set of exponents `k` such that `2 ^ (k + 1) - 1` is prime. -/

def mersennePrimeExponents : Set ℕ := {k | (mersenne (k + 1)).Prime}

/-- The map `k ↦ 2 ^ k - 1` is strictly monotone. -/

theorem mersenne_strictMono : StrictMono mersenne := by
  refine strictMono_nat_of_lt_succ fun n => ?_
  have h : 0 < 2 ^ n := Nat.two_pow_pos n
  simp only [mersenne, pow_succ]
  omega

/-- The Euclid map `k ↦ 2 ^ k * (2 ^ (k + 1) - 1)` is strictly monotone. -/

theorem euclidMap_strictMono : StrictMono fun k : ℕ => 2 ^ k * mersenne (k + 1) := by
  refine strictMono_nat_of_lt_succ fun n => ?_
  have h1 : (2 : ℕ) ^ n < 2 ^ (n + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
  have h2 : mersenne (n + 1) < mersenne (n + 2) := mersenne_strictMono (by omega)
  exact Nat.mul_lt_mul_of_lt_of_lt h1 h2

/-- The Mersenne primes are exactly the values `2 ^ (k + 1) - 1` for `k` a Mersenne exponent. -/

theorem mersennePrimes_eq_image :
    mersennePrimes = (fun k : ℕ => mersenne (k + 1)) '' mersennePrimeExponents := by
  ext p
  constructor
  · rintro ⟨hp, k, rfl⟩
    match k with
    | 0 => simp [mersenne, Nat.not_prime_zero] at hp
    | (j + 1) => exact ⟨j, hp, rfl⟩
  · rintro ⟨k, hk, rfl⟩
    exact ⟨hk, k + 1, rfl⟩

/-- Euclid–Euler: the even perfect numbers are exactly the numbers `2 ^ k * (2 ^ (k + 1) - 1)`
for `k` a Mersenne exponent. -/

theorem evenPerfects_eq_image :
    evenPerfects = (fun k : ℕ => 2 ^ k * mersenne (k + 1)) '' mersennePrimeExponents := by
  ext n
  constructor
  · intro hn
    obtain ⟨k, hk, rfl⟩ := Theorems100.Nat.even_and_perfect_iff.mp hn
    exact ⟨k, hk, rfl⟩
  · rintro ⟨k, hk, rfl⟩
    exact Theorems100.Nat.even_and_perfect_iff.mpr ⟨k, hk, rfl⟩

/-- **Reduction of the Mersenne prime infinitude conjecture.**
There are infinitely many Mersenne primes if and only if there are infinitely many even perfect
numbers.  (Both statements are open; the equivalence is the Euclid–Euler theorem.) -/

theorem MersennePrimeInfinitude : mersennePrimes.Infinite ↔ evenPerfects.Infinite := by
  have h1 : Set.InjOn (fun k : ℕ => mersenne (k + 1)) mersennePrimeExponents :=
    (mersenne_strictMono.comp (strictMono_id.add_const 1)).injective.injOn
  have h2 : Set.InjOn (fun k : ℕ => 2 ^ k * mersenne (k + 1)) mersennePrimeExponents :=
    euclidMap_strictMono.injective.injOn
  rw [mersennePrimes_eq_image, evenPerfects_eq_image, Set.infinite_image_iff h1,
    Set.infinite_image_iff h2]

/-- Sanity check: `3 = 2 ^ 2 - 1` is a Mersenne prime, so the set is nonempty. -/
