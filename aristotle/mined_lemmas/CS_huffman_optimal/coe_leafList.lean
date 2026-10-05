import Mathlib

/-!
# Kraft's inequality for prefix-free codes
-/

namespace CS

open scoped BigOperators


theorem coe_leafList [Fintype α] :
    (↑(leafList α) : Multiset (HTree α)) = (Finset.univ : Finset α).val.map HTree.leaf := by
  rw [leafList, ← Multiset.map_coe, Finset.coe_toList]

