import RequestProject.Forest

open scoped BigOperators
open scoped Classical

set_option maxHeartbeats 1000000
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace CS

/-- The value computed by Huffman's algorithm on a multiset of weights. -/

lemma codeOf_node [DecidableEq ι] (l r : HTree ι) (i : ι) :
    codeOf (node l r) i = if i ∈ l.elems then false :: codeOf l i else true :: codeOf r i := rfl

/-- The code produced by a tree with distinct leaf labels is prefix free. -/
