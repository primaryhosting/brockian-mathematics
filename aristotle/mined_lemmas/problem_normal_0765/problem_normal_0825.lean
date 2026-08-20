
import Mathlib.Tactic

set_option quotPrecheck false
class Magma (G : Type _) where op : G → G → G
infixl:65 " ◇ " => Magma.op

/-
Problem normal_0765: eq1708 → eq3230
-/

theorem problem_normal_0825 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G), x = (y ◇ (z ◇ x)) ◇ y)
    : ∀ (x : G) (y : G) (z : G), x = x ◇ (((y ◇ z) ◇ y) ◇ x) := by
  grind

/-
Problem normal_0836: eq1287 → eq1445
-/
