
import Mathlib.Tactic

set_option quotPrecheck false
class Magma (G : Type _) where op : G → G → G
infixl:65 " ◇ " => Magma.op

/-
Problem normal_0765: eq1708 → eq3230
-/

theorem problem_normal_0925 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x = (y ◇ z) ◇ ((x ◇ w) ◇ u))
    : ∀ (x : G) (y : G) (z : G), x = (y ◇ y) ◇ (x ◇ z) := by
  intro x y z;
  convert h x y y z x using 1;
  grind

/-
Problem normal_0926: eq1911 → eq1557
-/
