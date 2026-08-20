import RequestProject.Forest

open scoped BigOperators
open scoped Classical

set_option maxHeartbeats 1000000
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace CS

/-- The value computed by Huffman's algorithm on a multiset of weights. -/

theorem huffman_le_expLength (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (c : ι → List Bool)
    (hc : IsPrefixCode c) : Hmul (Finset.univ.val.map w) ≤ expLength w c := by
  set s : Multiset (ℝ × ℕ) := Finset.univ.val.map (fun i => (w i, (c i).length)) with hs
  have hfst : s.map Prod.fst = Finset.univ.val.map w := by
    rw [hs, Multiset.map_map]
    rfl
  have hcost : mcost s = expLength w c := by
    rw [mcost, hs, Multiset.map_map, expLength, Finset.sum]
    rfl
  have hnn : ∀ p ∈ s, 0 ≤ p.1 := by
    intro p hp
    rw [hs] at hp
    obtain ⟨i, -, rfl⟩ := Multiset.mem_map.mp hp
    exact hw i
  have hkraft : mkraft s ≤ 1 := by
    have hL : PFList (Finset.univ.toList.map c) := by
      rw [PFList, List.pairwise_map]
      refine List.Pairwise.imp_of_mem ?_ ((Finset.nodup_toList (Finset.univ : Finset ι)))
      intro a b _ _ hab
      exact ⟨hc a b hab, hc b a (Ne.symm hab)⟩
    have hk := kraft_inequality _ hL
    have heq : mkraft s = kraftSum (Finset.univ.toList.map c) := by
      rw [mkraft_def, hs, kraftSum, Multiset.map_map, Multiset.map_map]
      rw [← Finset.coe_toList (Finset.univ : Finset ι)]
      rw [List.map_map]
      rfl
    rw [heq]
    exact hk
  have := huffman_le_of_kraft s.card s le_rfl hnn hkraft
  rw [hfst, hcost] at this
  exact this

/-- **Huffman coding is optimal**: the code produced by Huffman's algorithm is a prefix
code, and no prefix code has smaller expected codeword length. -/
