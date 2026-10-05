import Mathlib

/-!
# Kraft's inequality for prefix-free codes
-/

namespace CS

open scoped BigOperators


theorem encode_node_right [DecidableEq α] {l r : HTree α} {a : α} (h : a ∉ l.leaves) :
    (node l r).encode a = true :: r.encode a := by simp [encode, h]

/-- Distinct symbols of a tree with distinct leaves get codewords none of which is a
prefix of another. -/
