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
