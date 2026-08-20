import RequestProject.Forest

open scoped BigOperators
open scoped Classical

set_option maxHeartbeats 1000000
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace CS

/-- The value computed by Huffman's algorithm on a multiset of weights. -/

lemma mkraft_def (s : Multiset (ℝ × ℕ)) :
    mkraft s = ((s.map Prod.snd).map (fun l => (2 : ℝ)⁻¹ ^ l)).sum := rfl

/-- **Huffman's algorithm is optimal**, in terms of codeword lengths: the value it computes
is a lower bound for the expected length of any assignment of codeword lengths satisfying
Kraft's inequality. -/
