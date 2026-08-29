import Mathlib

/-!
# Kraft's inequality for prefix-free codes
-/

namespace CS

open scoped BigOperators


def encode [DecidableEq α] : HTree α → α → List Bool
  | leaf _, _ => []
  | node l r, a => if a ∈ l.leaves then false :: l.encode a else true :: r.encode a

