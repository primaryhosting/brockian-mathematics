/-
# Aronszajn Tree Exists
Category: Frontier — Set Theory
Target: Frontier.Aronszajn_tree_exists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open Ordinal Set Cardinal
open scoped Classical

namespace Frontier

/-- The first uncountable ordinal `ω₁`. -/

theorem Eaux_finOne (n : ℕ) : FinOne (Eaux a n) (cseq a n) := by
  induction n with
  | zero => rw [cseq_zero]; exact finOne_zero _
  | succ n ih =>
    intro v
    have hlt : cseq a (n + 1) < a := cseq_lt_self h0 hs (n + 1)
    obtain ⟨hfo, -⟩ := IH _ hlt
    refine Set.Finite.subset (((ih v).union (hfo v)).union (hfo.le_finite n)) ?_
    rintro x ⟨hx, hv⟩
    rw [Eaux_succ] at hv
    by_cases hxn : x < cseq a n
    · rw [if_pos hxn] at hv
      exact Or.inl (Or.inl ⟨hxn, hv⟩)
    · rw [if_neg hxn] at hv
      rcases Nat.lt_or_ge (E (cseq a (n + 1)) x) n with hlt' | hge
      · exact Or.inr ⟨hx, le_of_lt hlt'⟩
      · exact Or.inl (Or.inr ⟨hx, by rwa [max_eq_left hge] at hv⟩)

include h0 hs IH in
