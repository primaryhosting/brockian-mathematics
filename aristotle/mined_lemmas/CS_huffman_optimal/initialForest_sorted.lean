import RequestProject.Forest

open scoped BigOperators
open scoped Classical

set_option maxHeartbeats 1000000
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace CS

/-- The value computed by Huffman's algorithm on a multiset of weights. -/

lemma initialForest_sorted (w : ι → ℝ) :
    ((initialForest w).map Prod.fst).Pairwise (· ≤ ·) := by
  rw [List.pairwise_map]
  exact List.pairwise_insertionSort _ _

omit [DecidableEq ι] in
/-- The tree built by Huffman's algorithm: it has all symbols as leaves, and its cost is
the value computed by Huffman's algorithm on the multiset of weights. -/
