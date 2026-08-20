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

lemma finite_range_leftQuotient_one :
    (Set.range (1 : Language α).leftQuotient).Finite := by
  apply Set.Finite.subset (Set.toFinite {(1 : Language α), 0})
  rintro _ ⟨x, rfl⟩
  rcases x with _ | ⟨a, x⟩
  · exact Or.inl (by simp)
  · exact Or.inr (Set.mem_singleton_iff.mpr (lang_ext fun y => by simp))

