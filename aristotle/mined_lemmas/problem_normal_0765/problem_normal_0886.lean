
import Mathlib.Tactic

set_option quotPrecheck false
class Magma (G : Type _) where op : G → G → G
infixl:65 " ◇ " => Magma.op

/-
Problem normal_0765: eq1708 → eq3230
-/

theorem problem_normal_0886 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = ((z ◇ x) ◇ w) ◇ w)
    : ∀ (x : G) (y : G) (z : G), x ◇ x = ((y ◇ z) ◇ x) ◇ x := by
  intro x y z;
  convert h x x y z using 1;
  convert h _ _ _ _ using 1;
  rotate_left;
  exact x;
  exact x ◇ x;
  grind

/-
Problem normal_0888: eq1520 → eq1244
-/
