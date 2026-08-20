import RequestProject.Forest

open scoped BigOperators
open scoped Classical

set_option maxHeartbeats 1000000
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace CS

/-- The value computed by Huffman's algorithm on a multiset of weights. -/

lemma initialForest_perm (w : ι → ℝ) :
    (initialForest w).Perm (Finset.univ.toList.map (fun i => (w i, HTree.leaf i))) :=
  List.perm_insertionSort _ _

omit [DecidableEq ι] in
