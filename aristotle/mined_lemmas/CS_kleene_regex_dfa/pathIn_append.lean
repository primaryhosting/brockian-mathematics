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


theorem pathIn_append {l : List σ} {u : σ} (hu : u ∈ l) :
    ∀ (x : List α) (s : σ) (y : List α) (t : σ),
      PathIn M l s u x → PathIn M l u t y → PathIn M l s t (x ++ y) := by
  intro x
  induction x with
  | nil =>
    intro s y t hx hy
    obtain rfl : s = u := hx
    simpa using hy
  | cons a x ih =>
    rintro s y t (⟨h1, rfl⟩ | ⟨h1, h2⟩) hy
    · refine Or.inr ⟨h1 ▸ hu, ?_⟩
      simpa [h1] using hy
    · exact Or.inr ⟨h1, ih _ y t h2 hy⟩

