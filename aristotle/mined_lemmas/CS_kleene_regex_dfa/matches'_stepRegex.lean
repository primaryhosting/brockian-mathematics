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

theorem matches'_stepRegex (M : DFA α σ) (p q : σ) :
    (stepRegex M p q).matches' = {w : List α | ∃ a, w = [a] ∧ M.step p a = q} := by
  ext w
  rw [stepRegex, mem_matches'_sumRegex]
  constructor
  · rintro ⟨r, hr, hw⟩
    obtain ⟨a, -, rfl⟩ := List.mem_map.mp hr
    by_cases h : M.step p a = q
    · rw [if_pos h, RegularExpression.matches'_char] at hw
      exact ⟨a, Set.mem_singleton_iff.mp hw, h⟩
    · rw [if_neg h, RegularExpression.matches'_zero] at hw
      exact absurd hw (Language.notMem_zero _)
  · rintro ⟨a, rfl, ha⟩
    refine ⟨if M.step p a = q then RegularExpression.char a else 0,
      List.mem_map.mpr ⟨a, by simp, rfl⟩, ?_⟩
    rw [if_pos ha, RegularExpression.matches'_char]
    rfl

/-- Kleene's algorithm: `kleeneRegex M l p q` matches the words taking `M` from `p` to `q`
with all intermediate states in `l`. -/
