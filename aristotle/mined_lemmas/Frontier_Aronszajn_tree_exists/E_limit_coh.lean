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

theorem E_limit_coh (b : Ordinal) (hb : b < a) : Coh (E a) (E b) b := by
  have hc : (Set.Iio a).Countable := countable_Iio_of_lt ha
  obtain ⟨n, hn⟩ := cseq_cofinal hc hb
  obtain ⟨-, hcoh⟩ := IH _ (cseq_lt_self h0 hs n)
  refine Set.Finite.subset (((Eaux_coh h0 hs IH n).union (hcoh b hn))) ?_
  rintro x ⟨hx, hv⟩
  have hxn : x < cseq a n := lt_trans hx hn
  rw [E_eq_Eaux h0 hs hxn] at hv
  by_cases hEq : Eaux a n x = E (cseq a n) x
  · exact Or.inr ⟨hx, by rw [← hEq]; exact hv⟩
  · exact Or.inl ⟨hxn, hEq⟩

end LimitStage

/-! ### The specification of `E` -/

