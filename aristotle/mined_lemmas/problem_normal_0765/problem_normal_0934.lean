
import Mathlib.Tactic

set_option quotPrecheck false
class Magma (G : Type _) where op : G → G → G
infixl:65 " ◇ " => Magma.op

/-
Problem normal_0765: eq1708 → eq3230
-/

theorem problem_normal_0934 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = z ◇ (x ◇ (x ◇ w)))
    : ∀ (x : G) (y : G), x ◇ x = y ◇ ((y ◇ x) ◇ y) := by
  intro x y;
  convert h x x y x using 1;
  grind +revert

/-
Problem normal_0937: eq3062 → eq323
-/
