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
# Riesel Problem
Category: Brockian Conjecture
Target: Brockian.RieselCovering.RieselProblem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Brockian.RieselCovering

/-- The Riesel number under consideration: `509203`. -/

lemma coverPrime_mem (r : ℕ) : coverPrime r = 3 ∨ coverPrime r = 5 ∨ coverPrime r = 7 ∨
    coverPrime r = 13 ∨ coverPrime r = 17 ∨ coverPrime r = 241 := by
  rcases lt_or_ge r 24 with hr | hr
  · interval_cases r <;> simp [coverPrime]
  · left
    have hnone : ([3, 5, 3, 241, 3, 5, 3, 13, 3, 5, 3, 7,
        3, 5, 3, 17, 3, 5, 3, 13, 3, 5, 3, 7] : List ℕ)[r]? = none :=
      List.getElem?_eq_none (by simpa using hr)
    simp [coverPrime, List.getD_eq_getElem?_getD, hnone]

/-- Every member of the covering set is prime. -/
