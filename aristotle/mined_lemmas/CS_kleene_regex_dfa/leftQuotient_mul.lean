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

theorem leftQuotient_mul (A B : Language α) (a : α) :
    (A * B).leftQuotient [a] =
      A.leftQuotient [a] * B + (if [] ∈ A then B.leftQuotient [a] else 0) := by
  ext y
  rw [Language.mem_leftQuotient, Language.mem_add, Language.mem_mul, Language.mem_mul]
  constructor
  · rintro ⟨u, hu, v, hv, huv⟩
    cases u with
    | nil =>
        simp only [List.nil_append] at huv
        subst huv
        right
        rw [if_pos hu, Language.mem_leftQuotient]
        exact hv
    | cons b u =>
        rw [List.cons_append] at huv
        obtain ⟨rfl, rfl⟩ : b = a ∧ u ++ v = y := by simpa using huv
        exact Or.inl ⟨u, by rw [Language.mem_leftQuotient]; exact hu, v, hv, rfl⟩
  · rintro (⟨u, hu, v, hv, rfl⟩ | h)
    · rw [Language.mem_leftQuotient] at hu
      exact ⟨a :: u, hu, v, hv, by simp⟩
    · by_cases hA : [] ∈ A
      · rw [if_pos hA, Language.mem_leftQuotient] at h
        exact ⟨[], hA, a :: y, h, by simp⟩
      · rw [if_neg hA] at h
        exact absurd h (Language.notMem_zero _)

