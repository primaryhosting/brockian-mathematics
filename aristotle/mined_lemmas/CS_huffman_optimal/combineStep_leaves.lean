import Mathlib

/-!
# Kraft's inequality for prefix-free codes
-/

namespace CS

open scoped BigOperators


theorem combineStep_leaves (w : α → ℝ) (ts : List (HTree α)) (h : 2 ≤ ts.length) :
    msLeaves (↑(combineStep w ts)) = msLeaves (↑ts) := by
  obtain ⟨t1, t2, rest, hcs, hmul, _, _, _⟩ := combineStep_spec w ts h
  rw [hcs, hmul]
  have : (↑(HTree.node t1 t2 :: rest) : Multiset (HTree α))
      = HTree.node t1 t2 ::ₘ (↑rest : Multiset (HTree α)) := rfl
  rw [this]
  simp [add_assoc]

