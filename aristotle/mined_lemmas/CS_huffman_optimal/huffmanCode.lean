import RequestProject.Forest

open scoped BigOperators
open scoped Classical

set_option maxHeartbeats 1000000
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace CS

/-- The value computed by Huffman's algorithm on a multiset of weights. -/

noncomputable def huffmanCode (w : ι → ℝ) : ι → List Bool :=
  (hforest (initialForest w)).elim (fun _ => []) (fun T => HTree.codeOf T)

omit [Fintype ι] [DecidableEq ι] in
