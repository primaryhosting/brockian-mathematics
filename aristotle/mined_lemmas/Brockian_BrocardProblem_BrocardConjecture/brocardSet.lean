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

import Mathlib

/-!
# Brocard Conjecture
Category: Brockian Conjecture
Target: Brockian.BrocardProblem.BrocardConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset Filter UniqueFactorizationMonoid
open scoped Nat

namespace Brockian.BrocardProblem

/-- The `abc` conjecture, stated for natural numbers, using the radical
`UniqueFactorizationMonoid.radical` (the product of the distinct prime factors):
for every `ε > 0` there is a constant `K > 0` such that whenever `a + b = c` with
`a, b` positive and coprime, we have `c ≤ K * rad(a * b * c) ^ (1 + ε)`. -/

def brocardSet : Set ℕ := {n : ℕ | ∃ m : ℕ, n ! + 1 = m ^ 2}

/-- The radical of `n !` is at most `4 ^ n`: it is a product of distinct primes `≤ n`,
hence at most the primorial of `n`, which is at most `4 ^ n`. -/
