import RequestProject.Forest

open scoped BigOperators
open scoped Classical

set_option maxHeartbeats 1000000
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace CS

/-- The value computed by Huffman's algorithm on a multiset of weights. -/

noncomputable def mkraft (s : Multiset (ℝ × ℕ)) : ℝ :=
  ((s.map Prod.snd).map (fun l => (2 : ℝ)⁻¹ ^ l)).sum

