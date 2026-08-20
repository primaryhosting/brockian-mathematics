import RequestProject.Forest

open scoped BigOperators
open scoped Classical

set_option maxHeartbeats 1000000
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace CS

/-- The value computed by Huffman's algorithm on a multiset of weights. -/

lemma Hmul_of_card_le_one {m : Multiset ℝ} (h : m.card ≤ 1) : Hmul m = 0 := by
  unfold Hmul
  have hlen : (m.sort (· ≤ ·)).length ≤ 1 := by
    rw [Multiset.length_sort]; exact h
  match hm : m.sort (· ≤ ·) with
  | [] => simp
  | [a] => simp
  | a :: b :: t => rw [hm] at hlen; simp at hlen

/-- One step of Huffman's algorithm, at the level of multisets of weights. -/
