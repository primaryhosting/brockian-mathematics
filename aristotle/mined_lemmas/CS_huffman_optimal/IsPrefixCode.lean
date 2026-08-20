import RequestProject.Forest

open scoped BigOperators
open scoped Classical

set_option maxHeartbeats 1000000
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace CS

/-- The value computed by Huffman's algorithm on a multiset of weights. -/

def IsPrefixCode (c : ι → List Bool) : Prop := ∀ i j, i ≠ j → ¬ (c i <+: c j)

/-- The expected codeword length of the code `c` for the weights `w`. -/
