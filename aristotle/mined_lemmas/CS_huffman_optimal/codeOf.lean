import RequestProject.Forest

open scoped BigOperators
open scoped Classical

set_option maxHeartbeats 1000000
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace CS

/-- The value computed by Huffman's algorithm on a multiset of weights. -/

def codeOf [DecidableEq ι] : HTree ι → ι → List Bool
  | leaf _, _ => []
  | node l r, i => if i ∈ l.elems then false :: codeOf l i else true :: codeOf r i

