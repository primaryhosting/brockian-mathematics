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


theorem pathIn_mono {l l' : List σ} (hl : ∀ q ∈ l, q ∈ l') :
    ∀ (x : List α) (s t : σ), PathIn M l s t x → PathIn M l' s t x := by
  intro x
  induction x with
  | nil => intro s t h; exact h
  | cons a x ih =>
    rintro s t (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact Or.inl ⟨h1, h2⟩
    · exact Or.inr ⟨hl _ h1, ih _ _ h2⟩

