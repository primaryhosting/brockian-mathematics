import RequestProject.Forest

open scoped BigOperators
open scoped Classical

set_option maxHeartbeats 1000000
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace CS

/-- The value computed by Huffman's algorithm on a multiset of weights. -/

noncomputable def kraftSum (L : List (List Bool)) : ℝ :=
  (L.map (fun x => (2 : ℝ)⁻¹ ^ x.length)).sum

