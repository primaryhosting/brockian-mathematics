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

theorem pderivs_subset (r : RegularExpression α) (w : List α) {l : List (RegularExpression α)}
    (hl : ∀ p ∈ l, p ∈ r :: pdset r) : ∀ q ∈ pderivs l w, q ∈ r :: pdset r := by
  induction w generalizing l with
  | nil => simpa [pderivs] using hl
  | cons a w ih =>
    rw [pderivs]
    refine ih ?_
    intro q hq
    obtain ⟨p, hp, hq⟩ := List.mem_flatMap.1 hq
    rcases List.mem_cons.1 (hl p hp) with h | h
    · subst h
      exact List.mem_cons_of_mem _ (pderiv_mem_pdset hq)
    · exact List.mem_cons_of_mem _ (pdset_closed h hq)

/-- A language described by a regular expression has finitely many left quotients. -/
