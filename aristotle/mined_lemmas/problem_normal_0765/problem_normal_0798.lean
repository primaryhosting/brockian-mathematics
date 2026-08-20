
import Mathlib.Tactic

set_option quotPrecheck false
class Magma (G : Type _) where op : G → G → G
infixl:65 " ◇ " => Magma.op

/-
Problem normal_0765: eq1708 → eq3230
-/

theorem problem_normal_0798 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G) (w : G), x = y ◇ ((x ◇ (z ◇ w)) ◇ y))
    : ∀ (x : G) (y : G) (z : G) (w : G), x = y ◇ ((y ◇ z) ◇ (w ◇ z)) := by
  intro x y z;
  convert h x y z z using 1;
  grind

/-
Problem normal_0800: eq3819 → eq3957
-/
