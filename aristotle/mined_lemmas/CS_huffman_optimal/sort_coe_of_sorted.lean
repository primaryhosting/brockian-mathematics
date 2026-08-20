import RequestProject.Forest

open scoped BigOperators
open scoped Classical

set_option maxHeartbeats 1000000
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace CS

/-- The value computed by Huffman's algorithm on a multiset of weights. -/

lemma sort_coe_of_sorted {l : List ℝ} (hs : l.Pairwise (· ≤ ·)) :
    (↑l : Multiset ℝ).sort (· ≤ ·) = l := by
  refine List.Perm.eq_of_pairwise (fun a b _ _ h1 h2 => le_antisymm h1 h2)
    (Multiset.pairwise_sort _ _) hs ?_
  exact Multiset.coe_eq_coe.mp (Multiset.sort_eq _ _)

