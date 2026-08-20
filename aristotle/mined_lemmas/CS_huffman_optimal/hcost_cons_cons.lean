import RequestProject.Forest

open scoped BigOperators
open scoped Classical

set_option maxHeartbeats 1000000
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace CS

/-- The value computed by Huffman's algorithm on a multiset of weights. -/

lemma hcost_cons_cons (a b : ℝ) (rest : List ℝ) :
    hcost (a :: b :: rest) = (a + b) + hcost (List.orderedInsert (· ≤ ·) (a + b) rest) := by
  rw [hcost]

/-- Huffman's algorithm on a forest of weighted trees. -/
