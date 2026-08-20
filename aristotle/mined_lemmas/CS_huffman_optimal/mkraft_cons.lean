import RequestProject.Forest

open scoped BigOperators
open scoped Classical

set_option maxHeartbeats 1000000
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace CS

/-- The value computed by Huffman's algorithm on a multiset of weights. -/

@[simp] lemma mkraft_cons (p : ℝ × ℕ) (s : Multiset (ℝ × ℕ)) :
    mkraft (p ::ₘ s) = (2 : ℝ)⁻¹ ^ p.2 + mkraft s := by simp [mkraft]

