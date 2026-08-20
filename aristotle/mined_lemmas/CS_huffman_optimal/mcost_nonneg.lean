import RequestProject.Forest

open scoped BigOperators
open scoped Classical

set_option maxHeartbeats 1000000
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace CS

/-- The value computed by Huffman's algorithm on a multiset of weights. -/

lemma mcost_nonneg {s : Multiset (ℝ × ℕ)} (h : ∀ p ∈ s, 0 ≤ p.1) : 0 ≤ mcost s := by
  refine Multiset.sum_nonneg ?_
  intro x hx
  obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.mp hx
  exact mul_nonneg (h y hy) (Nat.cast_nonneg _)

/-- The sorted list of a sorted list is itself. -/
