import Mathlib

/-!
# Kraft's inequality for prefix-free codes
-/

namespace CS

open scoped BigOperators


noncomputable def huffmanTree [Fintype α] [Nonempty α] (w : α → ℝ) : HTree α :=
  (buildList w (leafList α)).headD (HTree.leaf (Classical.arbitrary α))

