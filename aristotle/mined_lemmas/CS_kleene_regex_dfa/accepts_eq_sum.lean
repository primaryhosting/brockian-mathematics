import Mathlib

/-!
# Antimirov partial derivatives and finiteness of left quotients

This file develops Antimirov's partial derivatives of a regular expression, and uses them to
show that a language described by a regular expression has only finitely many left quotients.
Combined with the Myhill–Nerode theorem this gives the "regular expression → DFA" direction of
Kleene's theorem.
-/

namespace CS

open RegularExpression

variable {α : Type*}

/-- The language of a set of regular expressions: the union of the languages they describe. -/

theorem accepts_eq_sum [Fintype σ] [DecidablePred (· ∈ M.accept)] :
    M.accepts = ∑ j ∈ Finset.univ.filter (fun j => j ∈ M.accept),
      pathLang M Finset.univ M.start j := by
  ext w
  rw [mem_finset_sum]
  constructor
  · intro hw
    refine ⟨M.eval w, ?_, rfl, fun u v _ _ _ => Finset.mem_univ _⟩
    simpa using (DFA.mem_accepts M).1 hw
  · rintro ⟨j, hj, hwj, -⟩
    simp only [Finset.mem_filter] at hj
    rw [DFA.mem_accepts M]
    have hev : M.eval w = j := hwj
    rw [hev]
    exact hj.2

end DFAPath

/-- **Kleene, other direction**: a regular language is described by a regular expression. -/
