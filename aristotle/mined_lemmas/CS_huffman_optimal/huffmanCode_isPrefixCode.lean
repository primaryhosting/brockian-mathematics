import RequestProject.Forest

open scoped BigOperators
open scoped Classical

set_option maxHeartbeats 1000000
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace CS

/-- The value computed by Huffman's algorithm on a multiset of weights. -/

theorem huffmanCode_isPrefixCode (w : ι → ℝ) : IsPrefixCode (huffmanCode w) := by
  rcases List.eq_nil_or_concat (Finset.univ.toList (α := ι)) with hnil | ⟨l, a, hcon⟩
  · intro i j _
    exact absurd (Finset.mem_toList.mpr (Finset.mem_univ i)) (by rw [hnil]; simp)
  · have hne : Finset.univ.toList (α := ι) ≠ [] := by
      rw [hcon]; simp
    obtain ⟨T, hT, hperm, -⟩ := exists_huffman_tree w hne
    have hnd : T.elems.Nodup := hperm.nodup_iff.mpr (Finset.nodup_toList _)
    intro i j hij
    rw [huffmanCode_eq w hT]
    refine HTree.codeOf_prefixFree T hnd i ?_ j ?_ hij
    · exact hperm.mem_iff.mpr (Finset.mem_toList.mpr (Finset.mem_univ i))
    · exact hperm.mem_iff.mpr (Finset.mem_toList.mpr (Finset.mem_univ j))

/-- The expected length of the Huffman code is the value computed by Huffman's algorithm. -/
