
import Mathlib.Tactic

set_option quotPrecheck false
class Magma (G : Type _) where op : G → G → G
infixl:65 " ◇ " => Magma.op

/-
Problem normal_0765: eq1708 → eq3230
-/

theorem problem_normal_0941 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G) (w : G), x = (y ◇ z) ◇ ((x ◇ z) ◇ w))
    : ∀ (x : G) (y : G) (z : G), x ◇ x = y ◇ (y ◇ z) := by
  intro x y z;
  have := h x y x x;
  grind

/-
Problem normal_0949: eq892 → eq1818
-/
