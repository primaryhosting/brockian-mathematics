
import Mathlib.Tactic

set_option quotPrecheck false
class Magma (G : Type _) where op : G → G → G
infixl:65 " ◇ " => Magma.op

/-
Problem normal_0765: eq1708 → eq3230
-/

theorem problem_normal_0836 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G), x = y ◇ (((x ◇ y) ◇ x) ◇ z))
    : ∀ (x : G) (y : G), x = (x ◇ y) ◇ (x ◇ (y ◇ y)) := by
  intro x y;
  convert h x ( ‹Magma G›.op x y ) ( ‹Magma G›.op y y ) using 1;
  grind +ring

/-
Problem normal_0844: eq1973 → eq2445
-/
