import RequestProject.Forest

open scoped BigOperators
open scoped Classical

set_option maxHeartbeats 1000000
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace CS

/-- The value computed by Huffman's algorithm on a multiset of weights. -/

@[simp] lemma wsum_node (w : ι → ℝ) (l r : HTree ι) :
    wsum w (node l r) = wsum w l + wsum w r := by simp [wsum]

/-- The cost (weighted external path length) of a tree. -/
