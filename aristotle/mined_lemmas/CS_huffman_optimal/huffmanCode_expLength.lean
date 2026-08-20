import RequestProject.Forest

open scoped BigOperators
open scoped Classical

set_option maxHeartbeats 1000000
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace CS

/-- The value computed by Huffman's algorithm on a multiset of weights. -/

theorem huffmanCode_expLength (w : ι → ℝ) :
    expLength w (huffmanCode w) = Hmul (Finset.univ.val.map w) := by
  rcases List.eq_nil_or_concat (Finset.univ.toList (α := ι)) with hnil | ⟨l, a, hcon⟩
  · have hempty : (Finset.univ : Finset ι) = ∅ := by
      have : (Finset.univ : Finset ι).val = 0 := by
        rw [← Finset.coe_toList, hnil]; rfl
      exact Finset.val_eq_zero.mp this
    have : (Finset.univ.val.map w) = 0 := by rw [hempty]; rfl
    rw [expLength, this, Hmul_of_card_le_one (by simp)]
    rw [Finset.sum_congr hempty (fun x hx => rfl)]
    simp
  · have hne : Finset.univ.toList (α := ι) ≠ [] := by
      rw [hcon]; simp
    obtain ⟨T, hT, hperm, hcost⟩ := exists_huffman_tree w hne
    have hnd : T.elems.Nodup := hperm.nodup_iff.mpr (Finset.nodup_toList _)
    rw [huffmanCode_eq w hT, ← hcost, HTree.tcost_eq_sum_codeOf w T hnd, expLength]
    rw [← Finset.sum_map_toList]
    exact ((hperm.map (fun i => w i * ((HTree.codeOf T i).length : ℝ))).sum_eq).symm

omit [DecidableEq ι] in
/-- Any prefix code has expected length at least the value computed by Huffman's
algorithm. -/
