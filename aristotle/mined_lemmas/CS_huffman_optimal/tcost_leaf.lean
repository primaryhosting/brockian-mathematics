import RequestProject.Forest

open scoped BigOperators
open scoped Classical

set_option maxHeartbeats 1000000
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace CS

/-- The value computed by Huffman's algorithm on a multiset of weights. -/

@[simp] lemma tcost_leaf (w : ι → ℝ) (i : ι) : tcost w (leaf i) = 0 := rfl

