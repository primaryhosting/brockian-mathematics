import RequestProject.Forest

open scoped BigOperators
open scoped Classical

set_option maxHeartbeats 1000000
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace CS

/-- The value computed by Huffman's algorithm on a multiset of weights. -/

lemma kraftSum_append (L₁ L₂ : List (List Bool)) :
    kraftSum (L₁ ++ L₂) = kraftSum L₁ + kraftSum L₂ := by
  simp [kraftSum]

