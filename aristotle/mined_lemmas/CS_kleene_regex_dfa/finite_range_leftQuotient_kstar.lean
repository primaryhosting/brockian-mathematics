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

lemma finite_range_leftQuotient_kstar {L : Language α}
    (h : (Set.range L.leftQuotient).Finite) :
    (Set.range (L∗).leftQuotient).Finite := by
  classical
  apply Set.Finite.subset (((Set.toFinite ({L∗, 0} : Set (Language α))).prod
      (h.image (fun N : Language α => N * L∗)).finite_subsets).image
    (fun p : Language α × Set (Language α) => p.1 + sSup p.2))
  rintro _ ⟨x, rfl⟩
  refine ⟨((if x ∈ L∗ then L∗ else 0),
      {N : Language α | ∃ v, (∃ u, u ∈ L∗ ∧ x = u ++ v) ∧ N = (L.leftQuotient v) * L∗}),
    ⟨?_, ?_⟩, (leftQuotient_kstar L x).symm⟩
  · by_cases hx : x ∈ L∗ <;> simp [hx]
  · rintro N ⟨v, -, rfl⟩
    exact ⟨L.leftQuotient v, ⟨v, rfl⟩, rfl⟩

/-- Every language matched by a regular expression has finitely many left quotients. -/
