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

