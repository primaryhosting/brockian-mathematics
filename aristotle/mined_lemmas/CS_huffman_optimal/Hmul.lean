import RequestProject.Forest

open scoped BigOperators
open scoped Classical

set_option maxHeartbeats 1000000
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace CS

/-- The value computed by Huffman's algorithm on a multiset of weights. -/

noncomputable def Hmul (m : Multiset ℝ) : ℝ := hcost (m.sort (· ≤ ·))

/-- The expected codeword length of a multiset of (weight, codeword length) pairs. -/
