import Mathlib

/-!
# Kraft's inequality for prefix-free codes
-/

namespace CS

open scoped BigOperators


def msLeaves (M : Multiset (HTree α)) : Multiset α := (M.map HTree.leaves).sum

