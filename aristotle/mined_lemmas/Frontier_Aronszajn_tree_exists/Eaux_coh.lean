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

theorem Eaux_coh (n : ℕ) : Coh (Eaux a n) (E (cseq a n)) (cseq a n) := by
  induction n with
  | zero => rw [cseq_zero]; exact coh_zero _ _
  | succ n ih =>
    have hlt : cseq a (n + 1) < a := cseq_lt_self h0 hs (n + 1)
    obtain ⟨hfo, hcoh⟩ := IH _ hlt
    have h2 : Coh (E (cseq a (n + 1))) (E (cseq a n)) (cseq a n) :=
      hcoh _ (cseq_mono a (Nat.lt_succ_self n))
    refine Set.Finite.subset ((ih.union h2.symm).union (hfo.le_finite n)) ?_
    rintro x ⟨hx, hv⟩
    rw [Eaux_succ] at hv
    by_cases hxn : x < cseq a n
    · rw [if_pos hxn] at hv
      by_cases hEq : Eaux a n x = E (cseq a n) x
      · exact Or.inl (Or.inr ⟨hxn, by rw [← hEq]; exact hv⟩)
      · exact Or.inl (Or.inl ⟨hxn, hEq⟩)
    · rw [if_neg hxn] at hv
      refine Or.inr ⟨hx, ?_⟩
      by_contra hcon
      exact hv (max_eq_left (le_of_lt (not_le.mp hcon)))

include ha h0 hs IH in
