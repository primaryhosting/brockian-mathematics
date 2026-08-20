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

theorem not_agree_to_disagree {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (p : Ω → ℝ) (hp0 : ∀ ω, 0 ≤ p ω) (hp1 : ∑ ω, p ω = 1)
    (I₁ I₂ : Ω → Finset Ω) (hI₁ : IsInfoPartition I₁) (hI₂ : IsInfoPartition I₂)
    (E M : Finset Ω) (ω₀ : Ω) (hω₀ : ω₀ ∈ M)
    (hCK : IsCommonKnowledgeEvent I₁ I₂ M)
    (q₁ q₂ : ℝ)
    (h₁ : ∀ ω ∈ M, 0 < prob p (I₁ ω) ∧ prob p (E ∩ I₁ ω) / prob p (I₁ ω) = q₁)
    (h₂ : ∀ ω ∈ M, 0 < prob p (I₂ ω) ∧ prob p (E ∩ I₂ ω) / prob p (I₂ ω) = q₂) :
    ¬ q₁ ≠ q₂ :=
  not_not_intro (aumann_agreement p hp0 hp1 I₁ I₂ hI₁ hI₂ E M ω₀ hω₀ hCK q₁ q₂ h₁ h₂)

/-! ### A concrete instance, showing the hypotheses above are satisfiable -/

section Example

open Finset

/-- Uniform common prior on four states. -/
