import RequestProject.Forest

open scoped BigOperators
open scoped Classical

set_option maxHeartbeats 1000000
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace CS

/-- The value computed by Huffman's algorithm on a multiset of weights. -/

noncomputable def mcost (s : Multiset (ℝ × ℕ)) : ℝ := (s.map (fun p => p.1 * (p.2 : ℝ))).sum

/-- The Kraft sum of a multiset of (weight, codeword length) pairs. -/
