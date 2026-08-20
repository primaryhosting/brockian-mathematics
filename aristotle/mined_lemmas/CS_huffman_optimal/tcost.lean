import RequestProject.Forest

open scoped BigOperators
open scoped Classical

set_option maxHeartbeats 1000000
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace CS

/-- The value computed by Huffman's algorithm on a multiset of weights. -/

def tcost (w : ι → ℝ) : HTree ι → ℝ
  | leaf _ => 0
  | node l r => tcost w l + tcost w r + wsum w l + wsum w r

