import RequestProject.Forest

open scoped BigOperators
open scoped Classical

set_option maxHeartbeats 1000000
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace CS

/-- The value computed by Huffman's algorithm on a multiset of weights. -/

lemma mkraft_congr {s t : Multiset (ℝ × ℕ)} (h : s.map Prod.snd = t.map Prod.snd) :
    mkraft s = mkraft t := by simp [mkraft, h]

