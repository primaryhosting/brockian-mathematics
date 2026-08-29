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


theorem matches'_baseRegex (s t : σ) : (baseRegex M s t).matches' = pathLang M [] s t := by
  ext x
  have hif : ((if s = t then 1 else 0 : RegularExpression α)).matches' =
      if s = t then (1 : Language α) else 0 := by
    by_cases hst : s = t <;> simp [hst]
  rw [baseRegex, RegularExpression.matches'_add, mem_add_language, hif,
    mem_matches'_letterRegex]
  simp only [mem_pathLang, Finset.mem_toList, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro (h | ⟨a, ha, rfl⟩)
    · by_cases hst : s = t
      · rw [if_pos hst] at h
        obtain rfl : x = [] := h
        exact hst
      · rw [if_neg hst] at h
        exact absurd h (Language.notMem_zero x)
    · exact Or.inl ⟨ha, rfl⟩
  · intro h
    match x with
    | [] =>
      left
      obtain rfl : s = t := h
      simp
    | b :: y =>
      rcases h with ⟨h1, rfl⟩ | ⟨h1, -⟩
      · exact Or.inr ⟨b, h1, rfl⟩
      · exact absurd h1 (by simp)

/-- Kleene's algorithm: the regular expression for paths from `s` to `t` whose intermediate
states all lie in `l`. -/
