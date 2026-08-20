import RequestProject.Forest

open scoped BigOperators
open scoped Classical

set_option maxHeartbeats 1000000
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace CS

/-- The value computed by Huffman's algorithm on a multiset of weights. -/

lemma codeOf_prefixFree [DecidableEq ι] :
    ∀ (T : HTree ι), T.elems.Nodup → ∀ i ∈ T.elems, ∀ j ∈ T.elems, i ≠ j →
      ¬ (codeOf T i <+: codeOf T j) := by
  intro T
  induction T with
  | leaf k =>
      intro _ i hi j hj hij
      simp only [elems_leaf, List.mem_singleton] at hi hj
      exact absurd (hi.trans hj.symm) hij
  | node l r ihl ihr =>
      intro hnd i hi j hj hij
      simp only [elems_node, List.nodup_append] at hnd
      obtain ⟨hl, hr, hdisj⟩ := hnd
      simp only [elems_node, List.mem_append] at hi hj
      by_cases hil : i ∈ l.elems <;> by_cases hjl : j ∈ l.elems
      · rw [codeOf_node, codeOf_node, if_pos hil, if_pos hjl]
        simpa using ihl hl i hil j hjl hij
      · have hjr : j ∈ r.elems := hj.resolve_left hjl
        rw [codeOf_node, codeOf_node, if_pos hil, if_neg hjl]
        simp
      · have hir : i ∈ r.elems := hi.resolve_left hil
        rw [codeOf_node, codeOf_node, if_neg hil, if_pos hjl]
        simp
      · have hir : i ∈ r.elems := hi.resolve_left hil
        have hjr : j ∈ r.elems := hj.resolve_left hjl
        rw [codeOf_node, codeOf_node, if_neg hil, if_neg hjl]
        simpa using ihr hr i hir j hjr hij

/-- The cost of a tree equals the weighted sum of the codeword lengths it assigns. -/
