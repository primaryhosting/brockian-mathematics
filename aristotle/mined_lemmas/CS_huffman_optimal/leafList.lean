import Mathlib

/-!
# Kraft's inequality for prefix-free codes
-/

namespace CS

open scoped BigOperators


def leafList [Fintype α] : List (HTree α) := (Finset.univ : Finset α).toList.map HTree.leaf

