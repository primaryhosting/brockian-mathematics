import Mathlib

/-!
# Kraft's inequality for prefix-free codes
-/

namespace CS

open scoped BigOperators


def leaves : HTree α → Multiset α
  | leaf a => {a}
  | node l r => l.leaves + r.leaves

