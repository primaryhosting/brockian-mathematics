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

theorem ram34 (G : SimpleGraph V) [DecidableRel G.Adj] (T : Finset V) (hT : 9 ≤ T.card) :
    RamF G T 3 4 := by
  obtain ⟨T', hT', hcard⟩ := Finset.exists_subset_card_eq hT
  refine RamF.mono hT' ?_
  clear hT' hT
  by_contra hcon
  -- in a counterexample every vertex would have exactly three neighbours
  have key : ∀ v ∈ T', (nbhd G T' v).card = 3 := by
    intro v hv
    have hsum := card_nbhd_add_card_nonNbhd (G := G) hv
    rw [hcard] at hsum
    have hup : ¬ (4 ≤ (nbhd G T' v).card) := fun h4 => hcon (ram_of_nbhd G T' v hv h4)
    have hlow : ¬ ((nbhd G T' v).card ≤ 2) := by
      intro h2
      have h6 : 6 ≤ (nonNbhd G T' v).card := by omega
      rcases ram33 G (nonNbhd G T' v) h6 with ⟨s, hs, hcl⟩ | ⟨s, hs, hcl⟩
      · exact hcon (Or.inl ⟨s, hs.trans nonNbhd_subset, hcl⟩)
      · refine hcon (Or.inr ?_)
        rw [nonNbhd_eq_compl_nbhd] at hs
        exact nclique_insert_nbhd hv hs hcl
    omega
  -- but then the sum of the degrees is 27, contradicting handshake parity
  have hsum : ∑ v ∈ T', (nbhd G T' v).card = 27 := by
    rw [Finset.sum_congr rfl key, Finset.sum_const, hcard, smul_eq_mul]
  have heven := even_sum_nbhd_card (G := G) T'
  rw [hsum] at heven
  exact (Nat.not_even_iff_odd.2 (by decide)) heven

/-- Ramsey `R(4,4) ≤ 18`. -/
