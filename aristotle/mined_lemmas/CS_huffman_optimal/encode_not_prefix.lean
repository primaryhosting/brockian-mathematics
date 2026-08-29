import Mathlib

/-!
# Kraft's inequality for prefix-free codes
-/

namespace CS

open scoped BigOperators


theorem encode_not_prefix [DecidableEq α] :
    ∀ (t : HTree α), t.leaves.Nodup → ∀ a ∈ t.leaves, ∀ b ∈ t.leaves, a ≠ b →
      ¬ (t.encode a <+: t.encode b) := by
  intro t
  induction t with
  | leaf x =>
      intro _ a ha b hb hab
      simp only [leaves_leaf, Multiset.mem_singleton] at ha hb
      exact absurd (ha.trans hb.symm) hab
  | node l r ihl ihr =>
      intro hnd a ha b hb hab
      rw [leaves_node, Multiset.nodup_add] at hnd
      obtain ⟨hl, hr, hdisj⟩ := hnd
      simp only [leaves_node, Multiset.mem_add] at ha hb
      by_cases hal : a ∈ l.leaves
      · by_cases hbl : b ∈ l.leaves
        · rw [encode_node_left hal, encode_node_left hbl, List.cons_prefix_cons]
          exact fun h => ihl hl a hal b hbl hab h.2
        · have hbr : b ∈ r.leaves := hb.resolve_left hbl
          rw [encode_node_left hal, encode_node_right hbl, List.cons_prefix_cons]
          simp
      · have har : a ∈ r.leaves := ha.resolve_left hal
        by_cases hbl : b ∈ l.leaves
        · rw [encode_node_right hal, encode_node_left hbl, List.cons_prefix_cons]
          simp
        · have hbr : b ∈ r.leaves := hb.resolve_left hbl
          rw [encode_node_right hal, encode_node_right hbl, List.cons_prefix_cons]
          exact fun h => ihr hr a har b hbr hab h.2

/-- The cost of a tree is the weighted sum of the codeword lengths. -/
