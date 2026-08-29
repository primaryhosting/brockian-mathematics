import Mathlib

/-!
# Kraft's inequality for prefix-free codes
-/

namespace CS

open scoped BigOperators


theorem encode_node_left [DecidableEq α] {l r : HTree α} {a : α} (h : a ∈ l.leaves) :
    (node l r).encode a = false :: l.encode a := by simp [encode, h]

