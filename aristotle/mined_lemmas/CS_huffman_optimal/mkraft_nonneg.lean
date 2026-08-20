import RequestProject.Forest

open scoped BigOperators
open scoped Classical

set_option maxHeartbeats 1000000
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace CS

/-- The value computed by Huffman's algorithm on a multiset of weights. -/

lemma mkraft_nonneg (s : Multiset (ℝ × ℕ)) : 0 ≤ mkraft s := by
  refine Multiset.sum_nonneg ?_
  intro x hx
  obtain ⟨y, -, rfl⟩ := Multiset.mem_map.mp hx
  positivity

