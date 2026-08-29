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

def Faithful (sys : RegulatedSystem S R Z) : Prop :=
  ∀ s s' : S, (∀ r : R, (sys.outcome s r = sys.goal ↔ sys.outcome s' r = sys.goal)) → s = s'

/-- **The regulator is an isomorphic model of the system.**  For a faithful, tight
system, a good regulator `ρ` is injective, and hence induces an equivalence between the
system's state space `S` and the set of regulator states actually used, which sends each
system state to the action the regulator takes on it.  This is the sharpest form of
"every good regulator is a model of the system": the regulator's internal state space is
an isomorphic copy of the system's state space. -/
