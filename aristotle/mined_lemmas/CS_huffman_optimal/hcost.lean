import RequestProject.Forest

open scoped BigOperators
open scoped Classical

set_option maxHeartbeats 1000000
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace CS

/-- The value computed by Huffman's algorithm on a multiset of weights. -/

noncomputable def hcost : List ℝ → ℝ
  | [] => 0
  | [_] => 0
  | a :: b :: rest => (a + b) + hcost (List.orderedInsert (· ≤ ·) (a + b) rest)
  termination_by l => l.length
  decreasing_by
    simp only [List.length_cons]
    have h := (List.perm_orderedInsert (· ≤ ·) (a + b) rest).length_eq
    simp only [List.length_cons] at h
    omega

