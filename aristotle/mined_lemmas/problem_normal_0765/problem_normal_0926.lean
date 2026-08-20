
import Mathlib.Tactic

set_option quotPrecheck false
class Magma (G : Type _) where op : G → G → G
infixl:65 " ◇ " => Magma.op

/-
Problem normal_0765: eq1708 → eq3230
-/

theorem problem_normal_0926 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G) (w : G), x = (y ◇ (x ◇ z)) ◇ (y ◇ w))
    : ∀ (x : G) (y : G) (z : G), x = (y ◇ z) ◇ (x ◇ (y ◇ y)) := by
  intro x y z;
  convert h x y z y using 1;
  have := h ( ‹Magma G›.op y z ) y ( ‹Magma G›.op x ( ‹Magma G›.op y y ) ) y;
  grind +suggestions

/-
Problem normal_0927: eq1683 → eq3531
-/
