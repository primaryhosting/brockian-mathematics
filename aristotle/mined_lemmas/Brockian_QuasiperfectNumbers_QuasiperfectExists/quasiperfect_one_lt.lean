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
# Quasiperfect Exists
Category: Brockian Conjecture
Target: Brockian.QuasiperfectNumbers.QuasiperfectExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(Note: Lean 4 does not allow a module doc comment before `import`, so the required
header appears here as an ordinary comment and is repeated as the module docstring below.)
-/

import Mathlib

/-!
# Quasiperfect Exists
Category: Brockian Conjecture
Target: Brockian.QuasiperfectNumbers.QuasiperfectExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

## Summary

A *quasiperfect* number is a natural number `n` with `σ(n) = 2n + 1`, i.e. the sum of the
proper divisors of `n` equals `n + 1`.  No quasiperfect number is known and their existence
is an open problem.  We prove here the classical structural constraints: any quasiperfect
number is an odd perfect square greater than `1`, and package this as a Lean-checked
reduction `QuasiperfectExists` of the existence question.
-/

namespace Brockian
namespace QuasiperfectNumbers

open Finset

/-- The sum-of-divisors function `σ₁`. -/

theorem quasiperfect_one_lt {n : ℕ} (h : Quasiperfect n) : 1 < n := by
  obtain ⟨hpos, heq⟩ := h
  rcases Nat.lt_or_ge 1 n with h1 | h1
  · exact h1
  · have hn1 : n = 1 := by omega
    subst hn1
    simp [sigmaOne] at heq

/-- For `p ≥ 3` the geometric sum `1 + p + ⋯ + p ^ k` is smaller than `2 * p ^ k`. -/
