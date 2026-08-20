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

theorem isRegular_of_isRegexLang {L : Language α} (h : IsRegexLang L) : L.IsRegular := by
  obtain ⟨r, rfl⟩ := h
  exact Language.IsRegular.of_finite_range_leftQuotient (finite_range_leftQuotient_matches' r)

end PartA

/-! ## Part B: from DFAs to regular expressions, via Kleene's algorithm -/

section PartB

variable {α : Type u} {σ : Type v} (M : DFA α σ)

/-- The set of words that take state `i` to state `j`, all of whose intermediate states
lie in the finite set `S`. -/
