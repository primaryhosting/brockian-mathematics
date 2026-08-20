import RequestProject.Forest

open scoped BigOperators
open scoped Classical

set_option maxHeartbeats 1000000
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace CS

/-- The value computed by Huffman's algorithm on a multiset of weights. -/

@[simp] lemma tcost_node (w : ι → ℝ) (l r : HTree ι) :
    tcost w (node l r) = tcost w l + tcost w r + wsum w l + wsum w r := rfl

/-- The codeword assigned to a symbol by a tree: the path from the root to its leaf. -/
