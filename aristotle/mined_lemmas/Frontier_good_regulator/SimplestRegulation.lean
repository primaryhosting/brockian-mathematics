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

namespace Frontier

/-!
# The Conant–Ashby "good regulator" theorem (deterministic base case)

Setting: a system with a set `S` of disturbances, a regulator with a set `R` of possible
actions, and a set `Z` of outcomes.  The outcome of the joint system is given by
`psi : R → S → Z`, and a (deterministic) regulator is a map `rho : S → R` choosing an
action for each disturbance.

* Regulation is *perfect* / the regulator is *good* when the outcome is constantly the
  target value `z0` (this is the base case `H(Z) = 0` of the entropy formulation:
  the outcome variable is deterministic).
* The regulator is *simplest* when, for each disturbance, at most one action attains the
  target outcome (Conant and Ashby's restriction to regulators with no superfluous
  variety).

The system, as it presents itself to the regulator, is the map `s ↦ psi · s`, i.e. the
"column" of the outcome table belonging to the disturbance `s`; we call it `systemMap`.
A regulator *is (contains) a model of the system* when its action is a function of that
column alone, i.e. `rho` factors through `systemMap`.

`Frontier.good_regulator` states exactly this: every simplest good regulator is a model
of the system.
-/

/-- The system as seen by the regulator: for a disturbance `s`, the map sending a
regulator action `r` to the resulting outcome `psi r s`. -/

def SimplestRegulation {R S Z : Type*} (psi : R → S → Z) (z0 : Z) : Prop :=
  ∀ (s : S) (r r' : R), psi r s = z0 → psi r' s = z0 → r = r'

/-- `rho` *is (contains) a model of the system* `psi`: the regulator's action depends on
the disturbance only through the system's behaviour `systemMap psi s`, i.e. `rho` factors
as `M ∘ systemMap psi` for some map `M`, which is thus a model of the system inside the
regulator. -/
