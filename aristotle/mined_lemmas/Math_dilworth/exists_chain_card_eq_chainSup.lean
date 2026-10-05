/-
# Dilworth
Category: Pure Mathematics
Target: Math.dilworth
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (The header above uses `/- -/` rather than `/-! -/` because Lean 4 does not allow a module
-- docstring to precede the `import` commands; the module docstring is repeated below.)

import Mathlib

/-!
# Dilworth
Category: Pure Mathematics
Target: Math.dilworth
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false

namespace Math

open Classical in
/-- The largest cardinality of a chain contained in the finset `t`. -/

lemma exists_chain_card_eq_chainSup (t : Finset α) :
    ∃ s : Finset α, s ⊆ t ∧ IsChain (· ≤ ·) (↑s : Set α) ∧ s.card = chainSup t := by
  classical
  have hne : t.powerset.Nonempty := ⟨∅, Finset.empty_mem_powerset t⟩
  obtain ⟨s, hs, hsup⟩ := Finset.exists_mem_eq_sup t.powerset hne
    (fun s : Finset α => if IsChain (· ≤ ·) (↑s : Set α) then s.card else 0)
  by_cases hc : IsChain (· ≤ ·) (↑s : Set α)
  · exact ⟨s, Finset.mem_powerset.mp hs, hc, by simp [chainSup, hsup, hc]⟩
  · refine ⟨∅, Finset.empty_subset t, by simp [Set.Subsingleton.isChain], ?_⟩
    simp [chainSup, hsup, hc]

