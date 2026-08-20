import RequestProject.Forest

open scoped BigOperators
open scoped Classical

set_option maxHeartbeats 1000000
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace CS

/-- The value computed by Huffman's algorithm on a multiset of weights. -/

lemma exists_huffman_tree (w : ι → ℝ) (hne : Finset.univ.toList (α := ι) ≠ []) :
    ∃ T : HTree ι, hforest (initialForest w) = some T ∧
      T.elems.Perm (Finset.univ.toList) ∧
      HTree.tcost w T = Hmul (Finset.univ.val.map w) := by
  have hF0ne : initialForest w ≠ [] := by
    intro h
    have hlen := (initialForest_perm w).length_eq
    rw [h] at hlen
    simp only [List.length_nil, List.length_map] at hlen
    exact hne (List.eq_nil_of_length_eq_zero hlen.symm)
  obtain ⟨T, hT⟩ := hforest_isSome (initialForest w) hF0ne
  have hwsum : ∀ p ∈ initialForest w, p.1 = HTree.wsum w p.2 := by
    intro p hp
    have : p ∈ Finset.univ.toList.map (fun i => (w i, HTree.leaf i)) :=
      (initialForest_perm w).mem_iff.mp hp
    obtain ⟨i, -, rfl⟩ := List.mem_map.mp this
    simp
  obtain ⟨hElems, hCost⟩ := hforest_spec w (initialForest w) T hT hwsum
  refine ⟨T, hT, ?_, ?_⟩
  · refine hElems.trans ?_
    have h1 : ((initialForest w).flatMap (fun p => p.2.elems)).Perm
        ((Finset.univ.toList.map (fun i => (w i, HTree.leaf i))).flatMap
          (fun p => p.2.elems)) := (initialForest_perm w).flatMap_right _
    refine h1.trans ?_
    rw [List.flatMap_map]
    simp
  · -- the cost
    have hzero : ((initialForest w).map (fun p => HTree.tcost w p.2)).sum = 0 := by
      refine List.sum_eq_zero ?_
      intro x hx
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
      have : p ∈ Finset.univ.toList.map (fun i => (w i, HTree.leaf i)) :=
        (initialForest_perm w).mem_iff.mp hp
      obtain ⟨i, -, rfl⟩ := List.mem_map.mp this
      simp
    have hsortEq : (Finset.univ.val.map w).sort (· ≤ ·) = (initialForest w).map Prod.fst := by
      have hcoe : (((initialForest w).map Prod.fst : List ℝ) : Multiset ℝ)
          = Finset.univ.val.map w := by
        have h1 : ((initialForest w : List (ℝ × HTree ι)) : Multiset (ℝ × HTree ι))
            = ((Finset.univ.toList.map (fun i => (w i, HTree.leaf i)) :
                List (ℝ × HTree ι)) : Multiset (ℝ × HTree ι)) :=
          Quot.sound (initialForest_perm w)
        calc (((initialForest w).map Prod.fst : List ℝ) : Multiset ℝ)
            = ((initialForest w : List (ℝ × HTree ι)) : Multiset (ℝ × HTree ι)).map Prod.fst := rfl
          _ = ((Finset.univ.toList.map (fun i => (w i, HTree.leaf i)) :
                List (ℝ × HTree ι)) : Multiset (ℝ × HTree ι)).map Prod.fst := by rw [h1]
          _ = Finset.univ.val.map w := by
              rw [← Multiset.map_coe, Multiset.map_map, Finset.coe_toList]
              rfl
      rw [← hcoe, sort_coe_of_sorted (initialForest_sorted w)]
    rw [hCost, hzero, Hmul, hsortEq, zero_add]

