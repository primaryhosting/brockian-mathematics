import RequestProject.Forest

open scoped BigOperators
open scoped Classical

set_option maxHeartbeats 1000000
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace CS

/-- The value computed by Huffman's algorithm on a multiset of weights. -/

lemma kraftSum_perm {L₁ L₂ : List (List Bool)} (h : L₁.Perm L₂) :
    kraftSum L₁ = kraftSum L₂ := (h.map _).sum_eq

/-- A prefix free list containing the empty word is the singleton `[[]]`. -/
