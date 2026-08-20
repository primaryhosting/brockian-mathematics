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

theorem aumann_agreement_example : (1 : ℝ)/2 = 1/2 :=
  aumann_agreement exPrior (fun _ => by norm_num [exPrior])
    (by norm_num [exPrior]) exI₁ exI₂ exI₁_isInfoPartition exI₂_isInfoPartition
    exE univ 0 (mem_univ 0) (fun ω _ => ⟨subset_univ _, subset_univ _⟩)
    (1/2) (1/2) exPosterior₁ exPosterior₂

end Example

end Frontier

#print axioms Frontier.aumann_agreement
#print axioms Frontier.not_agree_to_disagree

