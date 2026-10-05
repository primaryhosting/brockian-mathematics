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


theorem pathIn_of_kstar {l : List σ} {q : σ} (hq : q ∈ l) {x : List α}
    (hx : x ∈ (pathLang M l q q)∗) : PathIn M l q q x := by
  obtain ⟨L, rfl, hL⟩ := Language.mem_kstar.mp hx
  clear hx
  induction L with
  | nil => simp
  | cons w ws ih =>
    rw [List.flatten_cons]
    exact pathIn_append M hq w q ws.flatten q (hL w List.mem_cons_self)
      (ih fun z hz => hL z (List.mem_cons_of_mem _ hz))

/-- Splitting a path off at its first visit to `q`. -/
