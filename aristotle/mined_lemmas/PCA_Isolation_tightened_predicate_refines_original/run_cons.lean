import Mathlib

/-!
# Tightened Predicate Refines Original
Category: Proof-Carrying Apps
Target: PCA.Isolation.tightened_predicate_refines_original
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace PCA.Isolation

variable {S A : Type*}

/-- The state reached from `s` by executing the finite action trace `l`
under the transition function `step`. -/

@[simp] theorem run_cons (step : S → A → S) (s : S) (a : A) (l : List A) :
    run step s (a :: l) = run step (step s a) l := rfl

/-- `tighten step P n` is the `n`-fold strengthening of the isolation predicate `P`:
a state satisfies it when `P` holds now and, after any single action, the
`(n-1)`-fold strengthening still holds. -/
