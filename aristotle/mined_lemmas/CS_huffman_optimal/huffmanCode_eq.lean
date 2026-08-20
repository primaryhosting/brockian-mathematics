import RequestProject.Forest

open scoped BigOperators
open scoped Classical

set_option maxHeartbeats 1000000
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace CS

/-- The value computed by Huffman's algorithm on a multiset of weights. -/

lemma huffmanCode_eq (w : ι → ℝ) {T : HTree ι} (hT : hforest (initialForest w) = some T) :
    huffmanCode w = HTree.codeOf T := by
  rw [huffmanCode, hT]
  rfl

/-- Huffman's algorithm produces a prefix code. -/
