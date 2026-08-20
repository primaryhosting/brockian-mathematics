import RequestProject.Forest

open scoped BigOperators
open scoped Classical

set_option maxHeartbeats 1000000
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace CS

/-- The value computed by Huffman's algorithm on a multiset of weights. -/

lemma elems_ne_nil (T : HTree ι) : T.elems ≠ [] := by
  induction T with
  | leaf i => simp
  | node l r ihl _ => simp [ihl]

/-- Total weight of the leaves of a tree. -/
