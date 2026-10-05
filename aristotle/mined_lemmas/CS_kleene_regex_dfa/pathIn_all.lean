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


theorem pathIn_all {l : List σ} (hl : ∀ q : σ, q ∈ l) (x : List α) (s t : σ) :
    PathIn M l s t x ↔ M.evalFrom s x = t := by
  induction x generalizing s with
  | nil => simp
  | cons a x ih =>
    rw [pathIn_cons_word, DFA.evalFrom_cons, ← ih (M.step s a)]
    constructor
    · rintro (⟨h1, rfl⟩ | ⟨-, h2⟩)
      · exact h1
      · exact h2
    · intro h
      exact Or.inr ⟨hl _, h⟩

