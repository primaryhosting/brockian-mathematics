import RequestProject.Forest

open scoped BigOperators
open scoped Classical

set_option maxHeartbeats 1000000
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace CS

/-- The value computed by Huffman's algorithm on a multiset of weights. -/

lemma kraftSum_cons (x : List Bool) (L : List (List Bool)) :
    kraftSum (x :: L) = (2 : ℝ)⁻¹ ^ x.length + kraftSum L := by simp [kraftSum]

