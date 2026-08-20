
import Mathlib.Tactic

set_option quotPrecheck false
class Magma (G : Type _) where op : G → G → G
infixl:65 " ◇ " => Magma.op

/-
Problem normal_0765: eq1708 → eq3230
-/

theorem problem_normal_0919 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G) (w : G), x = y ◇ (((x ◇ y) ◇ z) ◇ w))
    : ∀ (x : G) (y : G) (z : G) (w : G), (x ◇ y) ◇ y = (z ◇ x) ◇ w := by
  intro x y z;
  have := h ( ‹Magma G›.op ( ‹Magma G›.op x y ) y ) z z z;
  grind

/-
Problem normal_0922: eq1907 → eq1680
-/
