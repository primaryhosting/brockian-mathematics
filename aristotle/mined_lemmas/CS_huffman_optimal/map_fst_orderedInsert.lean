import RequestProject.Forest

open scoped BigOperators
open scoped Classical

set_option maxHeartbeats 1000000
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace CS

/-- The value computed by Huffman's algorithm on a multiset of weights. -/

lemma map_fst_orderedInsert (x : ℝ × HTree ι) :
    ∀ (l : List (ℝ × HTree ι)),
      (List.orderedInsert (fun p q : ℝ × HTree ι => p.1 ≤ q.1) x l).map Prod.fst
        = List.orderedInsert (· ≤ ·) x.1 (l.map Prod.fst) := by
  intro l
  induction l with
  | nil => simp [List.orderedInsert]
  | cons y ys ih =>
      by_cases h : x.1 ≤ y.1
      · simp [List.orderedInsert, h]
      · simp [List.orderedInsert, h, ih]

/-- Structure theorem for Huffman's algorithm on a forest: the resulting tree has the
leaves of the whole forest, and its cost is the sum of the costs of the trees of the
forest plus the value computed by Huffman's algorithm on the weights. -/
