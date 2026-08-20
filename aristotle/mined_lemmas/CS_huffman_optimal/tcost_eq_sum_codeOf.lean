import RequestProject.Forest

open scoped BigOperators
open scoped Classical

set_option maxHeartbeats 1000000
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace CS

/-- The value computed by Huffman's algorithm on a multiset of weights. -/

lemma tcost_eq_sum_codeOf [DecidableEq ι] (w : ι → ℝ) :
    ∀ (T : HTree ι), T.elems.Nodup →
      tcost w T = (T.elems.map (fun i => w i * ((codeOf T i).length : ℝ))).sum := by
  intro T
  induction T with
  | leaf k => intro _; simp
  | node l r ihl ihr =>
      intro hnd
      simp only [elems_node, List.nodup_append] at hnd
      obtain ⟨hl, hr, hdisj⟩ := hnd
      have hL : l.elems.map (fun i => w i * ((codeOf (node l r) i).length : ℝ))
          = l.elems.map (fun i => w i * ((codeOf l i).length : ℝ) + w i) := by
        refine List.map_congr_left ?_
        intro a ha
        rw [codeOf_node, if_pos ha]
        push_cast [List.length_cons]
        ring
      have hR : r.elems.map (fun i => w i * ((codeOf (node l r) i).length : ℝ))
          = r.elems.map (fun i => w i * ((codeOf r i).length : ℝ) + w i) := by
        refine List.map_congr_left ?_
        intro a ha
        have hna : a ∉ l.elems := fun h => hdisj a h a ha rfl
        rw [codeOf_node, if_neg hna]
        push_cast [List.length_cons]
        ring
      rw [tcost_node, elems_node, List.map_append, List.sum_append, hL, hR,
        List.sum_map_add, List.sum_map_add, ihl hl, ihr hr]
      simp only [wsum]
      ring

end HTree

end CS

import RequestProject.Tree

open scoped BigOperators
open scoped Classical

set_option maxHeartbeats 1000000
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace CS

variable {ι : Type*}

/-- Huffman's algorithm run on a list of weights: repeatedly merge the two smallest
weights, accumulating the merged weights.  For a sorted input this is exactly the total
cost of the Huffman code. -/
