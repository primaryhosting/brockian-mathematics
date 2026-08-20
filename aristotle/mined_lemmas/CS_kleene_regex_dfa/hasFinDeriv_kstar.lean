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

theorem hasFinDeriv_kstar {A : Language α} (hA : HasFinDeriv A) : HasFinDeriv (A∗) := by
  obtain ⟨F, hF, hcF, hAF⟩ := hA
  refine ⟨insert (A∗) ((fun S : Set (Language α) => sSup S * A∗) '' {S | S ⊆ F}),
    (hF.finite_subsets.image _).insert _, ?_, by simp⟩
  rintro L hL a
  rcases hL with rfl | ⟨S, hS, rfl⟩
  · rw [leftQuotient_kstar]
    refine Or.inr ⟨{A.leftQuotient [a]}, ?_,
      show sSup {A.leftQuotient [a]} * A∗ = A.leftQuotient [a] * A∗ by rw [sSup_singleton]⟩
    simpa using hcF _ hAF a
  · simp only [Set.mem_setOf_eq] at hS
    refine Or.inr ⟨(fun L : Language α => L.leftQuotient [a]) '' S ∪
        (if [] ∈ sSup S then {A.leftQuotient [a]} else ∅), ?_, ?_⟩
    · rintro L (⟨M, hM, rfl⟩ | hL)
      · exact hcF _ (hS hM) a
      · split at hL
        · rw [Set.mem_singleton_iff] at hL
          subst hL
          exact hcF _ hAF a
        · exact absurd hL (Set.notMem_empty _)
    · simp only
      rw [leftQuotient_mul, leftQuotient_kstar, sSup_union_language, add_mul, leftQuotient_sSup]
      by_cases h : [] ∈ sSup S
      · rw [if_pos h, if_pos h, sSup_singleton]
      · rw [if_neg h, if_neg h, sSup_empty_language, zero_mul, add_zero]

