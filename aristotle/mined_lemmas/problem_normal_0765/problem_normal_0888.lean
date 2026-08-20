
import Mathlib.Tactic

set_option quotPrecheck false
class Magma (G : Type _) where op : G → G → G
infixl:65 " ◇ " => Magma.op

/-
Problem normal_0765: eq1708 → eq3230
-/

theorem problem_normal_0888 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G), x = (y ◇ y) ◇ (x ◇ (y ◇ z)))
    : ∀ (x : G) (y : G) (z : G), x = x ◇ (((y ◇ x) ◇ z) ◇ x) := by
  grind +splitIndPred

/-
Problem normal_0890: eq136 → eq3964
-/
