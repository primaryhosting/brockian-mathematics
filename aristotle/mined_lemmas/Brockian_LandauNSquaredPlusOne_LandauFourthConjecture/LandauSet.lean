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

/-!
# Landau Fourth Conjecture
Category: Brockian Conjecture
Target: Brockian.LandauNSquaredPlusOne.LandauFourthConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/


open Filter Asymptotics

namespace Brockian
namespace LandauNSquaredPlusOne

/-! ## The statement

Landau's fourth problem asks whether there are infinitely many primes of the form `n ^ 2 + 1`.
This is an open problem, so the main theorem below is a *conditional reduction*: it derives the
conjecture from a Hardy–Littlewood style lower bound for the associated counting function.

Alongside it we prove a number of unconditional results:

* several reformulations of the conjecture (unboundedness of witnesses, unboundedness of the
  counting function, infinitude of the set of primes of the shape `n ^ 2 + 1`);
* the classical congruence restriction on the prime divisors of `n ^ 2 + 1`;
* the unconditional partial result that infinitely many primes divide *some* value `n ^ 2 + 1`.
-/

/-- The set of natural numbers `n` such that `n ^ 2 + 1` is prime. -/

def LandauSet : Set ℕ := {n : ℕ | Nat.Prime (n ^ 2 + 1)}

/-- The set of primes of the form `n ^ 2 + 1`. -/
