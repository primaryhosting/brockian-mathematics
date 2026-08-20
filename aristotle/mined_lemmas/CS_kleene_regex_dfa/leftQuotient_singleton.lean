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

theorem leftQuotient_singleton (a c : α) :
    ({[c]} : Language α).leftQuotient [a] = if a = c then 1 else 0 := by
  ext y
  rw [Language.mem_leftQuotient]
  by_cases h : a = c
  · subst h
    rw [if_pos rfl, Language.mem_one]
    constructor
    · intro hy
      have : a :: y = [a] := Set.mem_singleton_iff.mp hy
      simpa using this
    · rintro rfl
      rfl
  · rw [if_neg h]
    refine iff_of_false ?_ (Language.notMem_zero _)
    intro hy
    have : a :: y = [c] := Set.mem_singleton_iff.mp hy
    exact h (by simpa using congrArg (fun l => l.head?) this)

