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

theorem ram33 (G : SimpleGraph V) [DecidableRel G.Adj] (T : Finset V) (hT : 6 ≤ T.card) :
    RamF G T 3 3 := by
  obtain ⟨v, hv⟩ : ∃ v, v ∈ T := Finset.card_pos.1 (by omega)
  have hsum := card_nbhd_add_card_nonNbhd (G := G) hv
  by_cases h : 3 ≤ (nbhd G T v).card
  · exact ram_of_nbhd G T v hv h
  · refine RamF.of_compl (ram_of_nbhd Gᶜ T v hv ?_)
    rw [← nonNbhd_eq_compl_nbhd]
    omega

/-- Ramsey `R(3,4) ≤ 9`. -/
