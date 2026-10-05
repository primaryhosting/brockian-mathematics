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

/-- The probability of the (finite) event `S` under the weight function `p`. -/

theorem aumann_hypotheses_satisfiable :
    (∀ ω, 0 < unif ω) ∧ (∑ ω, unif ω = 1) ∧
    IsPartition K₁ ∧ IsPartition K₂ ∧ K₁ ≠ K₂ ∧
    IsCommonKnowledgeAt K₁ K₂ Finset.univ 0 ∧
    (∀ ω ∈ (Finset.univ : Finset (Fin 4)), prob unif (Ev ∩ K₁ ω) / prob unif (K₁ ω) = 1 / 2) ∧
    (∀ ω ∈ (Finset.univ : Finset (Fin 4)), prob unif (Ev ∩ K₂ ω) / prob unif (K₂ ω) = 1 / 2) := by
  refine ⟨fun ω => by norm_num [unif], by norm_num [unif], ⟨by decide, by decide⟩,
    ⟨by decide, by decide⟩, by decide, ⟨by decide, by decide, by decide⟩, ?_, ?_⟩
  · have hcards : ∀ ω : Fin 4, (Ev ∩ K₁ ω).card = 1 ∧ (K₁ ω).card = 2 := by decide
    intro ω _
    obtain ⟨h1, h2⟩ := hcards ω
    rw [unif_post _ _ (by omega), h1, h2]
    norm_num
  · have hcards : ∀ ω : Fin 4, (Ev ∩ K₂ ω).card = 1 ∧ (K₂ ω).card = 2 := by decide
    intro ω _
    obtain ⟨h1, h2⟩ := hcards ω
    rw [unif_post _ _ (by omega), h1, h2]
    norm_num

end Nonvacuity

#print axioms Frontier.aumann_agreement
#print axioms Frontier.aumann_hypotheses_satisfiable

end Frontier

