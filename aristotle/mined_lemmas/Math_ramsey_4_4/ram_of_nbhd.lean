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

theorem ram_of_nbhd (G : SimpleGraph V) [DecidableRel G.Adj] (T : Finset V) (v : V) (hv : v ∈ T)
    {q : ℕ} (hq : q ≤ (nbhd G T v).card) : RamF G T 3 q := by
  by_cases hex : ∃ a ∈ nbhd G T v, ∃ b ∈ nbhd G T v, a ≠ b ∧ G.Adj a b
  · obtain ⟨a, ha, b, hb, hab, hadj⟩ := hex
    refine Or.inl ⟨{v, a, b}, ?_, ?_⟩
    · intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl
      · exact hv
      · exact nbhd_subset ha
      · exact nbhd_subset hb
    · rw [SimpleGraph.is3Clique_triple_iff]
      exact ⟨adj_of_mem_nbhd ha, adj_of_mem_nbhd hb, hadj⟩
  · push_neg at hex
    have hcl : Gᶜ.IsClique (nbhd G T v : Finset V) := by
      intro a ha b hb hab
      exact ⟨hab, hex a (Finset.mem_coe.1 ha) b (Finset.mem_coe.1 hb) hab⟩
    obtain ⟨s, hs, hns⟩ := exists_nclique_of_clique hcl hq
    exact Or.inr ⟨s, hs.trans nbhd_subset, hns⟩

/-- Ramsey `R(3,3) ≤ 6`. -/
