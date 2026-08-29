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

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

/-- The information cell of an agent at state `ω`: the set of states the agent, whose
information is described by the signal map `I`, cannot distinguish from `ω`. -/

theorem self_mem_cell {κ : Type*} [DecidableEq κ] (I : Ω → κ) (ω : Ω) : ω ∈ cell I ω := by
  simp

/-- **Aggregation over an information partition.**  If an event `C` is a union of cells of the
agent with signal map `I`, and on each such cell the conditional mass of `E` is the fixed
fraction `q` of the mass of the cell, then the same identity holds for `C` itself. -/
