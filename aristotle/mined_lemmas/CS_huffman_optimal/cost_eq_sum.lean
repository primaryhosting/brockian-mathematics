import Mathlib

/-!
# Kraft's inequality for prefix-free codes
-/

namespace CS

open scoped BigOperators


theorem cost_eq_sum [DecidableEq α] (w : α → ℝ) :
    ∀ (t : HTree α), t.leaves.Nodup →
      t.cost w = (t.leaves.map (fun a => w a * (t.encode a).length)).sum := by
  intro t
  induction t with
  | leaf x => simp
  | node l r ihl ihr =>
      intro hnd
      rw [leaves_node, Multiset.nodup_add] at hnd
      obtain ⟨hl, hr, hdisj⟩ := hnd
      have hL : (l.leaves.map (fun a => w a * ((node l r).encode a).length)).sum
          = (l.leaves.map w).sum + (l.leaves.map (fun a => w a * (l.encode a).length)).sum := by
        rw [← Multiset.sum_map_add]
        refine congrArg Multiset.sum (Multiset.map_congr rfl ?_)
        intro x hx
        rw [encode_node_left hx]
        simp
        ring
      have hR : (r.leaves.map (fun a => w a * ((node l r).encode a).length)).sum
          = (r.leaves.map w).sum + (r.leaves.map (fun a => w a * (r.encode a).length)).sum := by
        rw [← Multiset.sum_map_add]
        refine congrArg Multiset.sum (Multiset.map_congr rfl ?_)
        intro x hx
        rw [encode_node_right (Multiset.disjoint_right.mp hdisj hx)]
        simp
        ring
      rw [leaves_node, Multiset.map_add, Multiset.sum_add, hL, hR, cost_node,
        ihl hl, ihr hr, wt_eq_sum, wt_eq_sum]
      ring

end HTree

end CS

import RequestProject.Kraft

/-!
# Kraft sums of multisets of codeword lengths, and normalisation of length assignments

The key combinatorial content of the optimality of Huffman's algorithm is the following
*normalisation* statement: given a collection of weighted items together with a length
assignment satisfying Kraft's inequality, if `b1` and `b2` are two items of minimal weight,
then the lengths may be modified, without increasing the total cost and without breaking
Kraft's inequality, so that `b1` and `b2` receive the same (positive) length.
-/

namespace CS

/-- The Kraft sum `∑ 2 ^ (-k)` of a multiset of codeword lengths. -/
