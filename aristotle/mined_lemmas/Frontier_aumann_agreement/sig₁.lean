/-
# Aumann Agreement
Category: Frontier Mind
Target: Frontier.aumann_agreement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Aumann Agreement
Category: Frontier Mind
Target: Frontier.aumann_agreement
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

open Finset

variable {Ω ι κ : Type*} [Fintype Ω] [DecidableEq Ω]

/-- The information cell (element of the information partition) of an agent whose
information is described by the signal function `f`, at the state `ω`:
the set of states the agent cannot distinguish from `ω`. -/

def sig₁ : Fin 4 → ℕ := fun i => i.val / 2

/-- Agent 2's signal on the four-state space: it separates `{0,3}` from `{1,2}`. -/
