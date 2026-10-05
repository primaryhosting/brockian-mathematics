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
# Sierpinski Problem
Category: Brockian Conjecture
Target: Brockian.SierpinskiCovering.SierpinskiProblem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

set_option autoImplicit false

namespace Brockian
namespace SierpinskiCovering

/-- The covering table: for a residue `r` of the exponent modulo `36`, this list records a
small prime that divides `78557 * 2 ^ r + 1` (and also divides `2 ^ 36 - 1`, so that the
divisibility only depends on the exponent modulo `36`).

The primes used are `3, 5, 7, 13, 19, 37, 73`, which form the classical covering system
for the Sierpiński number `78557`. -/

lemma coverPrime_lt (n : ℕ) : coverPrime n < 78557 * 2 ^ n + 1 := by
  have h : coverPrime n ≤ 73 := (coverTable_spec' n).2.1
  have h2 : (1 : ℕ) ≤ 2 ^ n := Nat.one_le_two_pow
  nlinarith

/-- **The Sierpiński problem: `78557` is a Sierpiński number.**
For every natural number `n`, the number `78557 * 2 ^ n + 1` is composite (never prime).

The proof exhibits the classical covering system with the primes
`{3, 5, 7, 13, 19, 37, 73}`, each of which divides `2 ^ 36 - 1`, so that the residue of
`78557 * 2 ^ n + 1` modulo each of them depends only on `n % 36`. -/
