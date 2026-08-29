/-
# Ramsey 4 4
Category: Pure Mathematics
Target: Math.ramsey_4_4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

open scoped BigOperators

set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

namespace Math

open Finset SimpleGraph

/-- Extract four elements in increasing order from a four-element finset. -/

theorem ram44 (G : SimpleGraph V) [DecidableRel G.Adj] (T : Finset V) (hT : 18 ≤ T.card) :
    RamF G T 4 4 := by
  obtain ⟨v, hv⟩ : ∃ v, v ∈ T := Finset.card_pos.1 (by omega)
  have hsum := card_nbhd_add_card_nonNbhd (G := G) hv
  by_cases h : 9 ≤ (nbhd G T v).card
  · rcases ram34 G (nbhd G T v) h with ⟨s, hs, hcl⟩ | ⟨s, hs, hcl⟩
    · exact Or.inl (nclique_insert_nbhd hv hs hcl)
    · exact Or.inr ⟨s, hs.trans nbhd_subset, hcl⟩
  · have h9 : 9 ≤ (nbhd Gᶜ T v).card := by rw [← nonNbhd_eq_compl_nbhd]; omega
    refine RamF.of_compl ?_
    rcases ram34 Gᶜ (nbhd Gᶜ T v) h9 with ⟨s, hs, hcl⟩ | ⟨s, hs, hcl⟩
    · exact Or.inl (nclique_insert_nbhd hv hs hcl)
    · exact Or.inr ⟨s, hs.trans nbhd_subset, hcl⟩

end Upper

section Lower

/-- Adjacency of the Paley graph on 17 vertices: `i ~ j` iff `j - i` is a nonzero
quadratic residue mod 17. -/
