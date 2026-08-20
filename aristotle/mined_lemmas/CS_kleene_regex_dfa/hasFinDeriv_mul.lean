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

theorem hasFinDeriv_mul {A B : Language α} (hA : HasFinDeriv A) (hB : HasFinDeriv B) :
    HasFinDeriv (A * B) := by
  obtain ⟨F, hF, hcF, hAF⟩ := hA
  obtain ⟨G, hG, hcG, hBG⟩ := hB
  refine ⟨(fun p : Language α × Set (Language α) => p.1 * B + sSup p.2) ''
      (F ×ˢ {S | S ⊆ G}), (hF.prod hG.finite_subsets).image _, ?_,
      ⟨(A, ∅), ⟨hAF, by simp⟩, show A * B + sSup (∅ : Set (Language α)) = A * B by
        rw [sSup_empty_language, add_zero]⟩⟩
  rintro _ ⟨⟨X, S⟩, ⟨hX, hS⟩, rfl⟩ a
  simp only [Set.mem_setOf_eq] at hS
  refine ⟨(X.leftQuotient [a],
      (fun L : Language α => L.leftQuotient [a]) '' S ∪
        (if [] ∈ X then {B.leftQuotient [a]} else ∅)), ⟨hcF _ hX a, ?_⟩, ?_⟩
  · rintro L (⟨M, hM, rfl⟩ | hL)
    · exact hcG _ (hS hM) a
    · split at hL
      · rw [Set.mem_singleton_iff] at hL
        subst hL
        exact hcG _ hBG a
      · exact absurd hL (Set.notMem_empty _)
  · simp only
    rw [leftQuotient_add, leftQuotient_mul, leftQuotient_sSup, sSup_union_language]
    by_cases h : [] ∈ X
    · rw [if_pos h, if_pos h, sSup_singleton]
      abel
    · rw [if_neg h, if_neg h, sSup_empty_language]
      abel

