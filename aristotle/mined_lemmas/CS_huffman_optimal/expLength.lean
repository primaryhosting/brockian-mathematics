import RequestProject.Forest

open scoped BigOperators
open scoped Classical

set_option maxHeartbeats 1000000
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace CS

/-- The value computed by Huffman's algorithm on a multiset of weights. -/

noncomputable def expLength (w : ι → ℝ) (c : ι → List Bool) : ℝ :=
  ∑ i, w i * ((c i).length : ℝ)

/-- The initial forest of Huffman's algorithm: one leaf per symbol, sorted by weight. -/
