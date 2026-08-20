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

variable {Ω : Type*} [DecidableEq Ω]

/-- The prior probability of a (finite) event `S`, computed from the point masses `p`. -/

def IsInfoPartition (I : Ω → Finset Ω) : Prop :=
  (∀ ω, ω ∈ I ω) ∧ ∀ ω ω' : Ω, ω' ∈ I ω → I ω' = I ω

/-- An event `M` is *common knowledge* (between the two agents with information partitions
`I₁` and `I₂`) at every one of its states when it is a union of cells of each agent: from any
state of `M`, neither agent considers a state outside `M` possible, and this reasoning iterates
to all orders. -/
