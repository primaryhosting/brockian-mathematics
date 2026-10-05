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

section Aumann

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω] {κ : Type*} [DecidableEq κ]

/-- The prior probability of an event `S ⊆ Ω`, for a weight function `p : Ω → ℝ`. -/

def prob (p : Ω → ℝ) (S : Finset Ω) : ℝ := ∑ ω ∈ S, p ω

/-- An agent's information structure is encoded by a labelling map `part : Ω → κ`:
the agent, at state `ω`, learns exactly the label `part ω`, i.e. the agent's
information cell at `ω` is the set of states carrying the same label. -/
