import RequestProject.Forest

open scoped BigOperators
open scoped Classical

set_option maxHeartbeats 1000000
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace CS

/-- The value computed by Huffman's algorithm on a multiset of weights. -/

private lemma sum_tail_len : ∀ (M : List (List Bool)), (∀ x ∈ M, x ≠ []) →
    ((M.map List.tail).map List.length).sum + M.length = (M.map List.length).sum := by
  intro M
  induction M with
  | nil => simp
  | cons y ys ih =>
      intro h
      have hy : y ≠ [] := h y (by simp)
      have hrest : ∀ x ∈ ys, x ≠ [] := fun x hx => h x (by simp [hx])
      have := ih hrest
      cases y with
      | nil => exact absurd rfl hy
      | cons c cs => simp at this ⊢; omega

