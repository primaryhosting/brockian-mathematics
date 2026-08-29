/-
# Ramsey 3 4
Category: Pure Mathematics
Target: Math.ramsey_3_4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Ramsey 3 4
Category: Pure Mathematics
Target: Math.ramsey_3_4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset SimpleGraph

namespace Math

/-- The `(3,4)`-Ramsey property for `n`: every simple graph on `n` vertices contains
either a triangle (a `3`-clique) or an independent set of size `4`. -/

theorem ramsey_34_upper : RamseyProp34 9 := by
  intro G
  classical
  by_contra hcon
  push_neg at hcon
  obtain ⟨h3, h4⟩ := hcon
  -- No vertex has four neighbours: they would form an independent set of size 4.
  have hdeg_le : ∀ v : Fin 9, G.degree v ≤ 3 := by
    intro v
    by_contra hd
    push_neg at hd
    have hcard : 4 ≤ (G.neighborFinset v).card := by
      rw [SimpleGraph.card_neighborFinset_eq_degree]; omega
    obtain ⟨t, hts, ht4⟩ := Finset.exists_subset_card_eq hcard
    refine h4 t ⟨?_, ht4⟩
    intro a ha b hb hab hadj
    have hva : G.Adj v a := SimpleGraph.mem_neighborFinset .. |>.mp (hts ha)
    have hvb : G.Adj v b := SimpleGraph.mem_neighborFinset .. |>.mp (hts hb)
    exact h3 {v, a, b} (SimpleGraph.is3Clique_triple_iff.mpr ⟨hva, hvb, hadj⟩)
  -- Every vertex has at least three neighbours: otherwise its six non-neighbours would
  -- contain a triangle or an independent triple, the latter extending to an independent 4-set.
  have hdeg_ge : ∀ v : Fin 9, 3 ≤ G.degree v := by
    intro v
    by_contra hd
    push_neg at hd
    have hvnot : v ∉ G.neighborFinset v := by simp
    have hcard_ins : (insert v (G.neighborFinset v)).card = G.degree v + 1 := by
      rw [Finset.card_insert_of_notMem hvnot, SimpleGraph.card_neighborFinset_eq_degree]
    have hcard : 6 ≤ ((Finset.univ : Finset (Fin 9)) \ insert v (G.neighborFinset v)).card := by
      have hsub := Finset.card_univ_diff (insert v (G.neighborFinset v))
      rw [hsub, hcard_ins]
      simp only [Fintype.card_fin]
      omega
    have hmem : ∀ w ∈ (Finset.univ : Finset (Fin 9)) \ insert v (G.neighborFinset v),
        w ≠ v ∧ ¬ G.Adj v w := by
      intro w hw
      simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_insert,
        SimpleGraph.mem_neighborFinset, not_or] at hw
      exact hw
    rcases ramsey_33_on G ((Finset.univ : Finset (Fin 9)) \ insert v (G.neighborFinset v))
      hcard with ⟨t, hts, ht⟩ | ⟨t, hts, ht⟩
    · exact h3 t ht
    · have hvt : v ∉ t := fun hvt => ((hmem v (hts hvt)).1) rfl
      refine h4 (insert v t) ⟨?_, ?_⟩
      · intro a ha b hb hab
        simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe] at ha hb
        rcases ha with rfl | ha
        · rcases hb with rfl | hb
          · exact absurd rfl hab
          · exact (hmem b (hts hb)).2
        · rcases hb with rfl | hb
          · exact fun hadj => (hmem a (hts ha)).2 hadj.symm
          · exact ht.1 ha hb hab
      · rw [Finset.card_insert_of_notMem hvt, ht.2]
  -- Hence the graph is 3-regular on 9 vertices, contradicting the handshake lemma.
  have hdeg : ∀ v : Fin 9, G.degree v = 3 := fun v => le_antisymm (hdeg_le v) (hdeg_ge v)
  have hsum : ∑ v : Fin 9, G.degree v = 2 * G.edgeFinset.card :=
    SimpleGraph.sum_degrees_eq_twice_card_edges G
  rw [Finset.sum_congr rfl (fun v _ => hdeg v)] at hsum
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hsum
  omega

/-- The circulant graph on `ℤ/8` with connection set `{±1, 4}` (the Wagner graph). It is
triangle-free and has independence number 3, witnessing `R(3,4) > 8`. -/
