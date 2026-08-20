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

theorem leftQuotient_mem_of_derivClosed {F : Set (Language α)} (hc : DerivClosed F) :
    ∀ (x : List α) (L : Language α), L ∈ F → L.leftQuotient x ∈ F := by
  intro x
  induction x with
  | nil => intro L hL; simpa using hL
  | cons a x ih =>
      intro L hL
      have hx : L.leftQuotient (a :: x) = (L.leftQuotient [a]).leftQuotient x := by
        rw [← Language.leftQuotient_append]
        rfl
      rw [hx]
      exact ih _ (hc L hL a)

/-- A language lying in a finite derivative-closed family is regular. -/
