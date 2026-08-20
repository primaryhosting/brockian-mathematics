import RequestProject.Forest

open scoped BigOperators
open scoped Classical

set_option maxHeartbeats 1000000
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace CS

/-- The value computed by Huffman's algorithm on a multiset of weights. -/

@[simp] lemma elems_node (l r : HTree ι) : (node l r).elems = l.elems ++ r.elems := rfl

