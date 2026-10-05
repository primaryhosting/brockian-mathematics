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

theorem aumann_agreement {κ₁ κ₂ : Type*} [DecidableEq κ₁] [DecidableEq κ₂]
    (w : Ω → ℝ) (E C : Finset Ω) (I₁ : Ω → κ₁) (I₂ : Ω → κ₂) (q₁ q₂ : ℝ)
    (hCne : C.Nonempty) (hpos : ∀ x ∈ C, 0 < w x)
    (hC₁ : ∀ ω ∈ C, cell I₁ ω ⊆ C) (hC₂ : ∀ ω ∈ C, cell I₂ ω ⊆ C)
    (h₁ : ∀ ω ∈ C, (∑ x ∈ cell I₁ ω ∩ E, w x) / (∑ x ∈ cell I₁ ω, w x) = q₁)
    (h₂ : ∀ ω ∈ C, (∑ x ∈ cell I₂ ω ∩ E, w x) / (∑ x ∈ cell I₂ ω, w x) = q₂) :
    q₁ = q₂ := by
  -- rewrite the posterior hypotheses in product form
  have h₁' : ∀ ω ∈ C, ∑ x ∈ cell I₁ ω ∩ E, w x = q₁ * ∑ x ∈ cell I₁ ω, w x := by
    intro ω hω
    have hcp : 0 < ∑ x ∈ cell I₁ ω, w x :=
      Finset.sum_pos (fun x hx => hpos x (hC₁ ω hω hx)) ⟨ω, self_mem_cell I₁ ω⟩
    rw [← h₁ ω hω, div_mul_cancel₀ _ (ne_of_gt hcp)]
  have h₂' : ∀ ω ∈ C, ∑ x ∈ cell I₂ ω ∩ E, w x = q₂ * ∑ x ∈ cell I₂ ω, w x := by
    intro ω hω
    have hcp : 0 < ∑ x ∈ cell I₂ ω, w x :=
      Finset.sum_pos (fun x hx => hpos x (hC₂ ω hω hx)) ⟨ω, self_mem_cell I₂ ω⟩
    rw [← h₂ ω hω, div_mul_cancel₀ _ (ne_of_gt hcp)]
  have e₁ : ∑ x ∈ C ∩ E, w x = q₁ * ∑ x ∈ C, w x :=
    mass_inter_eq_of_cells w E I₁ q₁ C hC₁ h₁'
  have e₂ : ∑ x ∈ C ∩ E, w x = q₂ * ∑ x ∈ C, w x :=
    mass_inter_eq_of_cells w E I₂ q₂ C hC₂ h₂'
  have hCpos : 0 < ∑ x ∈ C, w x := Finset.sum_pos hpos hCne
  have := e₁.symm.trans e₂
  exact mul_right_cancel₀ (ne_of_gt hCpos) this

end Frontier

#print axioms Frontier.aumann_agreement

