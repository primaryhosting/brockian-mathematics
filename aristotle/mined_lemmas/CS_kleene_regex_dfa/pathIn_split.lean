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


theorem pathIn_split {l : List σ} {q : σ} :
    ∀ (x : List α) (s t : σ), PathIn M (q :: l) s t x →
      PathIn M l s t x ∨
        ∃ y z, x = y ++ z ∧ y ≠ [] ∧ PathIn M l s q y ∧ PathIn M (q :: l) q t z := by
  intro x
  induction x with
  | nil => intro s t h; exact Or.inl h
  | cons a x ih =>
    rintro s t (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact Or.inl (Or.inl ⟨h1, h2⟩)
    · by_cases hq : M.step s a = q
      · refine Or.inr ⟨[a], x, rfl, by simp, ?_, ?_⟩
        · exact Or.inl ⟨hq, rfl⟩
        · rw [hq] at h2
          exact h2
      · have hml : M.step s a ∈ l := by
          rcases List.mem_cons.mp h1 with h | h
          · exact absurd h hq
          · exact h
        rcases ih (M.step s a) t h2 with h | ⟨y, z, rfl, hy, hyq, hz⟩
        · exact Or.inl (Or.inr ⟨hml, h⟩)
        · exact Or.inr ⟨a :: y, z, rfl, by simp, Or.inr ⟨hml, hyq⟩, hz⟩

