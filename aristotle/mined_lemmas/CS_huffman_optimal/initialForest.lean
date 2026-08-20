import RequestProject.Forest

open scoped BigOperators
open scoped Classical

set_option maxHeartbeats 1000000
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace CS

/-- The value computed by Huffman's algorithm on a multiset of weights. -/

noncomputable def initialForest (w : ι → ℝ) : List (ℝ × HTree ι) :=
  List.insertionSort (fun p q => p.1 ≤ q.1)
    (Finset.univ.toList.map (fun i => (w i, HTree.leaf i)))

/-- The code produced by Huffman's algorithm. -/
