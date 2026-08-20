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

lemma append_mem_kstar {L : Language α} {u v : List α} (hu : u ∈ L∗) (hv : v ∈ L∗) :
    u ++ v ∈ L∗ := by
  obtain ⟨U, rfl, hU⟩ := Language.mem_kstar.mp hu
  obtain ⟨V, rfl, hV⟩ := Language.mem_kstar.mp hv
  refine Language.mem_kstar.mpr ⟨U ++ V, by simp, ?_⟩
  intro y hy
  rcases List.mem_append.mp hy with h | h
  · exact hU y h
  · exact hV y h

end Star

/-! ## Part A: from regular expressions to DFAs, via Myhill–Nerode -/

section PartA

variable {α : Type u}

