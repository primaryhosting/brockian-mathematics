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

theorem exists_regularExpression_of_dfa [Fintype σ] (M : DFA α σ) :
    ∃ R : RegularExpression α, R.matches' = M.accepts := by
  classical
  refine ⟨sumRegex ((Finset.univ : Finset σ).toList.map
    (fun q => if q ∈ M.accept then kleeneRegex M (Finset.univ : Finset σ).toList M.start q
      else 0)), ?_⟩
  have huniv : {x : σ | x ∈ (Finset.univ : Finset σ).toList} = (Set.univ : Set σ) := by
    ext x; simp
  ext w
  rw [mem_matches'_sumRegex, DFA.mem_accepts, DFA.eval]
  constructor
  · rintro ⟨r, hr, hw⟩
    obtain ⟨q, -, rfl⟩ := List.mem_map.mp hr
    by_cases hq : q ∈ M.accept
    · rw [if_pos hq, matches'_kleeneRegex, huniv] at hw
      rw [(mem_pathLang.mp hw).evalFrom]
      exact hq
    · rw [if_neg hq, RegularExpression.matches'_zero] at hw
      exact absurd hw (Language.notMem_zero _)
  · intro hw
    refine ⟨if M.evalFrom M.start w ∈ M.accept then
      kleeneRegex M (Finset.univ : Finset σ).toList M.start (M.evalFrom M.start w) else 0,
      List.mem_map.mpr ⟨M.evalFrom M.start w, by simp, rfl⟩, ?_⟩
    rw [if_pos hw, matches'_kleeneRegex, huniv]
    exact pathVia_univ rfl

end CS

import Mathlib

/-!
# Finite derivative families and regularity

This file develops an "Antimirov style" argument showing that every language matched by a
regular expression is regular (i.e. accepted by a DFA): we exhibit, for each regular expression,
a finite family of languages containing its language and closed under taking left quotients by
single letters.  Combined with the Myhill–Nerode theorem in Mathlib this gives regularity.
-/

universe u

open scoped Computability

attribute [local instance] Classical.propDecidable

namespace CS

variable {α : Type u}

/-! ### Basic facts about suprema of families of languages -/

