import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Math

/-- `RamseyProp s t n` says that for every graph `G` on `n` vertices (equivalently, every
two-colouring of the edges of the complete graph on `n` vertices) either `G` contains a clique
of size `s`, or the complement of `G` contains a clique of size `t` (i.e. `G` contains an
independent set of size `t`). -/

theorem ramseyProp_three_four_nine : RamseyProp 3 4 9 := by
  intro G
  by_contra hc
  push_neg at hc
  obtain ⟨hT, hI⟩ := hc
  classical
  have htri : ∀ a b c : Fin 9, G.Adj a b → G.Adj a c → G.Adj b c → False := by
    intro a b c h1 h2 h3
    exact hT {a, b, c} (SimpleGraph.is3Clique_triple_iff.mpr ⟨h1, h2, h3⟩)
  have hind : ∀ t : Finset (Fin 9), t.card = 4 →
      (∀ a ∈ t, ∀ b ∈ t, a ≠ b → ¬ G.Adj a b) → False := by
    intro t ht hpw
    exact hI t ⟨fun a ha b hb hab => ⟨hab, hpw a ha b hb hab⟩, ht⟩
  -- No vertex has degree `≥ 4`: its neighbourhood would be an independent set of size `4`.
  have hdeg_le : ∀ v : Fin 9, G.degree v ≤ 3 := by
    intro v
    by_contra hlt
    push_neg at hlt
    have h4 : 4 ≤ (G.neighborFinset v).card := hlt
    obtain ⟨t, hts, htc⟩ := Finset.exists_subset_card_eq h4
    refine hind t htc ?_
    intro a ha b hb _ hadj
    exact htri v a b (SimpleGraph.mem_neighborFinset .. |>.mp (hts ha))
      (SimpleGraph.mem_neighborFinset .. |>.mp (hts hb)) hadj
  -- No vertex has degree `≤ 2`: the `≥ 6` non-neighbours contain an independent set of size `3`,
  -- which together with the vertex gives an independent set of size `4`.
  have hdeg_ge : ∀ v : Fin 9, 3 ≤ G.degree v := by
    intro v
    by_contra hlt
    push_neg at hlt
    have hdv : (G.neighborFinset v).card = G.degree v := rfl
    have hcard : 6 ≤ (Finset.univ \ insert v (G.neighborFinset v)).card := by
      have h1 := Finset.card_insert_le v (G.neighborFinset v)
      have h2 := Finset.card_sdiff_add_card_eq_card
        (Finset.subset_univ (insert v (G.neighborFinset v)))
      have h3 : (Finset.univ : Finset (Fin 9)).card = 9 := by simp
      omega
    obtain ⟨t, hts, htc, hpw⟩ := exists_indep_three G htri _ hcard
    have hmem : ∀ x ∈ t, x ≠ v ∧ ¬ G.Adj v x := by
      intro x hx
      have hx' := hts hx
      simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_insert,
        SimpleGraph.mem_neighborFinset, not_or] at hx'
      exact hx'
    have hvt : v ∉ t := fun h => (hmem v h).1 rfl
    refine hind (insert v t) ?_ ?_
    · rw [Finset.card_insert_of_notMem hvt, htc]
    · intro a ha b hb hab
      simp only [Finset.mem_insert] at ha hb
      rcases ha with rfl | ha
      · rcases hb with rfl | hb
        · exact absurd rfl hab
        · exact (hmem b hb).2
      · rcases hb with rfl | hb
        · exact fun h => (hmem a ha).2 h.symm
        · exact hpw a ha b hb hab
  -- Hence the graph is `3`-regular on `9` vertices, contradicting the handshake lemma.
  have hdeg : ∀ v : Fin 9, G.degree v = 3 := fun v => le_antisymm (hdeg_le v) (hdeg_ge v)
  have hsum := G.sum_degrees_eq_twice_card_edges
  rw [Finset.sum_congr rfl (fun v _ => hdeg v)] at hsum
  simp at hsum
  omega

/-- The circulant graph `C₈(1,4)` (the Wagner graph): vertices `Fin 8`, with `a` joined to `b`
iff `b - a ∈ {1, 4, 7}`. -/
