import RequestProject.Forest

open scoped BigOperators
open scoped Classical

set_option maxHeartbeats 1000000
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace CS

/-- The value computed by Huffman's algorithm on a multiset of weights. -/

private lemma kraft_half (L : List (List Bool)) (h : ∀ x ∈ L, x ≠ []) :
    kraftSum L = (2 : ℝ)⁻¹ * kraftSum (L.map List.tail) := by
  unfold kraftSum
  rw [List.map_map]
  rw [← List.sum_map_mul_left]
  refine congrArg List.sum (List.map_congr_left ?_)
  intro a ha
  have : a.length = (a.tail).length + 1 := by
    cases a with
    | nil => exact absurd rfl (h [] ha)
    | cons b bs => simp
  rw [this]
  simp [pow_succ]
  ring

