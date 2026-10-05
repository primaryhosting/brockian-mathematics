import Mathlib

/-!
# Kleene Regex Dfa
Category: Computer Science
Target: CS.kleene_regex_dfa
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
Kleene's theorem: over a finite alphabet, a language is denoted by a regular expression
if and only if it is accepted by a deterministic finite automaton with finitely many states.
-/

open Language Computability

namespace CS

variable {α : Type*}


theorem append_mem_kstar {A : Language α} {u v : List α} (hu : u ∈ A∗) (hv : v ∈ A∗) :
    u ++ v ∈ A∗ := by
  obtain ⟨L₁, rfl, hL₁⟩ := Language.mem_kstar.mp hu
  obtain ⟨L₂, rfl, hL₂⟩ := Language.mem_kstar.mp hv
  refine Language.mem_kstar.mpr ⟨L₁ ++ L₂, by simp, ?_⟩
  intro z hz
  rcases List.mem_append.mp hz with hz | hz
  · exact hL₁ z hz
  · exact hL₂ z hz

/-- Splitting a word of `A∗` at the position separating a prefix `x` from a suffix `y`. -/
