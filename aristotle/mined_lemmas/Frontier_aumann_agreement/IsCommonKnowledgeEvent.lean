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

def IsCommonKnowledgeEvent (I₁ I₂ : Ω → Finset Ω) (M : Finset Ω) : Prop :=
  ∀ ω ∈ M, I₁ ω ⊆ M ∧ I₂ ω ⊆ M

section Partition

variable {I : Ω → Finset Ω} {M : Finset Ω}

/-- Inside a union `M` of cells, the fibre of the cell map over a cell `C` is exactly `C`. -/
