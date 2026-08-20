import Mathlib

/-!
# Kleene Regex Dfa
Category: Computer Science
Target: CS.kleene_regex_dfa
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise
open scoped Computability
open scoped Classical

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace CS

universe u v

/-- A language is *regex-expressible* if some regular expression matches exactly it. -/

lemma finite_range_leftQuotient_mul {L₁ L₂ : Language α}
    (h₁ : (Set.range L₁.leftQuotient).Finite) (h₂ : (Set.range L₂.leftQuotient).Finite) :
    (Set.range (L₁ * L₂).leftQuotient).Finite := by
  apply Set.Finite.subset ((h₁.prod h₂.finite_subsets).image
    (fun p : Language α × Set (Language α) => p.1 * L₂ + sSup p.2))
  rintro _ ⟨x, rfl⟩
  refine ⟨(L₁.leftQuotient x,
      {N : Language α | ∃ v, (∃ u, u ∈ L₁ ∧ x = u ++ v) ∧ N = L₂.leftQuotient v}),
    ⟨⟨x, rfl⟩, ?_⟩, (leftQuotient_mul L₁ L₂ x).symm⟩
  rintro N ⟨v, -, rfl⟩
  exact ⟨v, rfl⟩

