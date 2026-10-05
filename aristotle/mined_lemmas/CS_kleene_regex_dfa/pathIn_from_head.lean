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


theorem pathIn_from_head {l : List σ} {q t : σ} {x : List α} (hx : PathIn M (q :: l) q t x) :
    x ∈ (pathLang M l q q)∗ * pathLang M l q t :=
  pathIn_from_head_aux M x.length x t le_rfl hx

/-- The state elimination step of Kleene's algorithm. -/
