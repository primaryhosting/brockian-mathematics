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


theorem exists_regex_of_dfa [Fintype σ] :
    ∃ r : RegularExpression α, r.matches' = M.accepts := by
  classical
  have hall : ∀ q : σ, q ∈ (Finset.univ : Finset σ).toList := fun q =>
    Finset.mem_toList.mpr (Finset.mem_univ q)
  refine ⟨unionRegex (fun t => pathRegex M (Finset.univ : Finset σ).toList M.start t)
      ((Finset.univ.filter (fun t : σ => t ∈ M.accept)).toList), ?_⟩
  ext x
  rw [mem_matches'_unionRegex]
  simp only [matches'_pathRegex, mem_pathLang, Finset.mem_toList,
    Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨t, ht, hp⟩
    have hx : M.evalFrom M.start x = t := (pathIn_all M hall x M.start t).mp hp
    show M.eval x ∈ M.accept
    rw [DFA.eval, hx]
    exact ht
  · intro hx
    have hx' : M.eval x ∈ M.accept := hx
    exact ⟨M.eval x, hx', (pathIn_all M hall x M.start (M.eval x)).mpr rfl⟩

end DFAToRegex

/-- **Kleene's theorem.** Over a finite alphabet, a language is denoted by a regular expression
if and only if it is accepted by a deterministic finite automaton with finitely many states. -/
