import Mathlib

/-!
# From DFAs to regular expressions

This file implements Kleene's algorithm: given a DFA with finitely many states over a finite
alphabet, we construct a regular expression matching exactly the language it accepts.

The construction proceeds by recursion on a list `l` of "allowed intermediate states":
`kleeneRegex M l p q` matches exactly the words labelling a path from `p` to `q` all of whose
intermediate states belong to `l`.
-/

universe u v

open scoped Computability

namespace CS

variable {α : Type u} {σ : Type v}

/-! ### Paths with restricted intermediate states -/

/-- `PathVia M S p q w` means that reading `w` takes the DFA `M` from state `p` to state `q`,
in such a way that every *intermediate* state (i.e. every state visited strictly between the
start and the end of the run) lies in `S`. -/
inductive PathVia (M : DFA α σ) (S : Set σ) : σ → σ → List α → Prop
  | nil (p : σ) : PathVia M S p p []
  | cons {p q : σ} (a : α) {w : List α} (h : PathVia M S (M.step p a) q w)
      (hm : w ≠ [] → M.step p a ∈ S) : PathVia M S p q (a :: w)

/-- The language of words labelling paths from `p` to `q` with intermediate states in `S`. -/

theorem mem_pathLang_empty {M : DFA α σ} {p q : σ} {w : List α} :
    PathVia M ∅ p q w ↔ (w = [] ∧ p = q) ∨ ∃ a, w = [a] ∧ M.step p a = q := by
  constructor
  · intro h
    cases h with
    | nil p => exact Or.inl ⟨rfl, rfl⟩
    | cons a h hm =>
        rename_i w
        rcases eq_or_ne w [] with rfl | hw
        · exact Or.inr ⟨a, rfl, PathVia.nil_iff.mp h⟩
        · exact absurd (hm hw) (Set.notMem_empty _)
  · rintro (⟨rfl, rfl⟩ | ⟨a, rfl, ha⟩)
    · exact PathVia.nil p
    · exact PathVia.cons a (PathVia.nil_iff.mpr ha) (by simp)

/-! ### Sums of regular expressions -/

/-- The sum of a list of regular expressions. -/
