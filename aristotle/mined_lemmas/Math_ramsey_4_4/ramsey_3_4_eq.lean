/-
# Ramsey 4 4
Category: Pure Mathematics
Target: Math.ramsey_4_4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Ramsey 4 4
Category: Pure Mathematics
Target: Math.ramsey_4_4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

open Finset SimpleGraph

/-! ### Generic clique helpers -/

section Helpers
variable {V : Type*} {G : SimpleGraph V}

/-- A set with no internal `G`-edges is a clique of the complement. -/

lemma ramsey_3_4_eq (hc : Fintype.card V = 9) (h3 : G.CliqueFree 3) :
    ∃ t : Finset V, Gᶜ.IsNClique 4 t := by
  classical
  by_contra hcon
  push_neg at hcon
  have h4 : Gᶜ.CliqueFree 4 := hcon
  have hdeg : ∀ v : V, (nbrs G v).card = 3 := by
    intro v
    have hsum := card_nbrs_add_card_nonnbrs (G := G) v
    have hup : (nbrs G v).card ≤ 3 := by
      by_contra hgt
      push_neg at hgt
      obtain ⟨t, hts, htc⟩ := Finset.exists_subset_card_eq (n := 4) (s := nbrs G v) (by omega)
      exact h4 t (compl_isNClique_of_neighbors htc (fun w hw => adj_of_mem_nbrs (hts hw)) h3)
    have hlow : 3 ≤ (nbrs G v).card := by
      by_contra hlt
      push_neg at hlt
      have hM : 6 ≤ (nonnbrs G v).card := by omega
      set M : Set V := ((nonnbrs G v : Finset V) : Set V) with hMdef
      have hcardM : 6 ≤ Fintype.card M := by simpa [hMdef] using hM
      obtain ⟨t, ht⟩ := ramsey_3_3 (G := G.induce M) hcardM
        (h3.comap (SimpleGraph.Embedding.induce M))
      obtain ⟨u, hu, hucl⟩ := lift_compl_clique ht
      refine h4 (insert v u) (hucl.insert ?_)
      intro b hb
      exact compl_adj_of_mem_nonnbrs (by simpa [hMdef] using hu b hb)
    omega
  have hdegree : ∀ v : V, G.degree v = 3 := by
    intro v
    rw [← hdeg v, nbrs_eq_neighborFinset]
    rfl
  have hsum := G.sum_degrees_eq_twice_card_edges
  rw [Finset.sum_congr rfl (fun v _ => hdegree v)] at hsum
  simp only [Finset.sum_const, Finset.card_univ, hc, smul_eq_mul] at hsum
  omega

/-- `R(3,4) ≤ 9`. -/
