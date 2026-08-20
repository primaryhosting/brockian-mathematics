import RequestProject.Forest

open scoped BigOperators
open scoped Classical

set_option maxHeartbeats 1000000
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace CS

/-- The value computed by Huffman's algorithm on a multiset of weights. -/

noncomputable def hforest : List (ℝ × HTree ι) → Option (HTree ι)
  | [] => none
  | [(_, t)] => some t
  | (a, s) :: (b, t) :: rest =>
      hforest (List.orderedInsert (fun p q => p.1 ≤ q.1) (a + b, HTree.node s t) rest)
  termination_by l => l.length
  decreasing_by
    simp only [List.length_cons]
    have h := (List.perm_orderedInsert (fun p q : ℝ × HTree ι => p.1 ≤ q.1)
      (a + b, HTree.node s t) rest).length_eq
    simp only [List.length_cons] at h
    omega

