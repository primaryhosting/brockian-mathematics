/-
Antimirov partial derivatives: every language matched by a regular expression is regular
(i.e. accepted by a DFA with finitely many states).
-/
import Mathlib

namespace CS

open RegularExpression Language Computability

universe u
variable {α : Type u}

/-! ### Membership lemmas for languages -/


theorem pds_subset (P : RegularExpression α) (x : List α) {q : RegularExpression α}
    (hq : q ∈ insert P (PD P)) : pds q x ⊆ insert P (PD P) := by
  induction x generalizing q with
  | nil => rw [pds_nil, Set.singleton_subset_iff]; exact hq
  | cons a x ih =>
      intro s hs
      rw [pds_cons, Set.mem_iUnion₂] at hs
      obtain ⟨p, hp, hs⟩ := hs
      have hpmem : p ∈ insert P (PD P) := by
        rcases hq with rfl | hq
        · exact Set.mem_insert_of_mem _ (pd_subset_PD q a hp)
        · exact Set.mem_insert_of_mem _ (pd_of_mem_PD P a q hq hp)
      exact ih hpmem hs

/-- The language of a set of regular expressions: the union of the languages they match. -/
