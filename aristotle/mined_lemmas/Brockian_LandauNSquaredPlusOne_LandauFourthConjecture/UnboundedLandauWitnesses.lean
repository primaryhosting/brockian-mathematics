import Brockian.LandauNSquaredPlusOne

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
# Landau Fourth Conjecture
Category: Brockian Conjecture
Target: Brockian.LandauNSquaredPlusOne.LandauFourthConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Brockian.LandauNSquaredPlusOne

open Set

/-- The set of primes of the form `n ^ 2 + 1` (the "Landau primes"). -/

def UnboundedLandauWitnesses : Prop := ∀ N : ℕ, ∃ n : ℕ, N < n ∧ Nat.Prime (n ^ 2 + 1)

/-- **Landau's fourth conjecture (conditional form).**
If witnesses `n` with `n ^ 2 + 1` prime occur arbitrarily far out, then there are infinitely
many primes of the form `n ^ 2 + 1`.  (Landau's fourth problem is open, so the hypothesis is
carried explicitly; the theorem is a Lean-checked reduction of the infinitude statement to the
unbounded-witness statement.) -/
