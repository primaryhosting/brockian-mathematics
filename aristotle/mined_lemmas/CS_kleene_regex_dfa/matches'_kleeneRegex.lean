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

theorem matches'_kleeneRegex (M : DFA α σ) :
    ∀ (l : List σ) (p q : σ), (kleeneRegex M l p q).matches' = pathLang M {x | x ∈ l} p q := by
  intro l
  induction l with
  | nil =>
      intro p q
      have hset : {x : σ | x ∈ ([] : List σ)} = (∅ : Set σ) := by ext x; simp
      rw [hset, kleeneRegex, RegularExpression.matches'_add, matches'_stepRegex]
      ext w
      rw [Language.mem_add, mem_pathLang, mem_pathLang_empty]
      constructor
      · rintro (h | h)
        · by_cases hpq : p = q
          · subst hpq
            rw [if_pos rfl] at h
            exact Or.inl ⟨Language.mem_one w |>.mp h, rfl⟩
          · rw [if_neg hpq] at h
            exact absurd h (Language.notMem_zero _)
        · exact Or.inr h
      · rintro (⟨rfl, rfl⟩ | h)
        · exact Or.inl (by rw [if_pos rfl]; exact Language.nil_mem_one)
        · exact Or.inr h
  | cons s l ih =>
      intro p q
      have hset : {x : σ | x ∈ s :: l} = insert s {x : σ | x ∈ l} := by
        ext x; simp [Set.mem_insert_iff]
      rw [kleeneRegex, RegularExpression.matches'_add, RegularExpression.matches'_mul,
        RegularExpression.matches'_mul, RegularExpression.matches'_star, ih, ih, ih, ih, hset,
        pathLang_insert]

/-- Every language accepted by a DFA with finitely many states over a finite alphabet is
matched by a regular expression. -/
