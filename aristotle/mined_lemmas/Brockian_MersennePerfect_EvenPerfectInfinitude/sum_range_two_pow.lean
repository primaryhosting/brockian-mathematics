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

lemma sum_range_two_pow (k : ℕ) : ∑ x ∈ range (k + 1), 2 ^ x = 2 ^ (k + 1) - 1 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, ih]
    have h : 1 ≤ 2 ^ (k + 1) := Nat.one_le_two_pow
    have : 2 ^ (k + 2) = 2 ^ (k + 1) + 2 ^ (k + 1) := by ring
    omega

/-- The Mersenne number `2 ^ (k+1) - 1` is odd. -/
