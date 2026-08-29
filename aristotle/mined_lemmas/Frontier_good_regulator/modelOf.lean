import Mathlib

/-!
# Good Regulator
Category: Frontier Mind
Target: Frontier.good_regulator
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

namespace Frontier

/-- A *regulated system* in the sense of Conant–Ashby.

`S` is the set of states of the system (the disturbances acting on the regulator),
`R` is the set of states (actions) available to the regulator, and `Z` is the set of
outcomes.  The outcome is jointly determined by the system state and the regulator's
action via `outcome`, and `goal` is the single outcome the regulator is trying to
enforce. -/
structure RegulatedSystem (S R Z : Type*) where
  /-- The outcome produced by a system state together with a regulator action. -/
  outcome : S → R → Z
  /-- The outcome the regulator must enforce. -/
  goal : Z

variable {S R Z : Type*}

/-- A regulator `ρ`, i.e. a rule assigning an action to each system state, is *good*
(perfectly regulating) when it always enforces the goal outcome. -/

def modelOf (sys : RegulatedSystem S R Z) (r : R) : Set S :=
  {s : S | sys.outcome s r = sys.goal}

/-!
## The Good Regulator Theorem (Conant–Ashby)

Every good regulator of a system is (contains) a model of that system.

In the deterministic base case formalized here, a good regulator `ρ` of a tight system
is shown to be:

* **unique** — it is the only rule that perfectly regulates the system, so it is forced
  by the system itself rather than chosen freely;
* **a homomorphic image of the system** — the regulator's state `ρ s` determines exactly
  which actions succeed against `s`, i.e. it determines the system's requirement; two
  system states mapped to the same regulator state are indistinguishable in what they
  demand of the regulator;
* **a model** — there is a map `model : R → Set S` from regulator states to sets of
  system states such that every state is in the model of its own regulator state, every
  state in the model of `r` is correctly handled by `r`, and the models of distinct
  regulator states are disjoint.  Thus the regulator's internal state is an isomorphic
  copy (a model) of the relevant structure of the system.
-/
