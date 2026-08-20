
import Mathlib.Tactic

set_option quotPrecheck false
class Magma (G : Type _) where op : G → G → G
infixl:65 " ◇ " => Magma.op

/-
Problem normal_0765: eq1708 → eq3230
-/

theorem problem_normal_0866 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x ◇ y = (z ◇ (w ◇ y)) ◇ u)
    : ∀ (x : G) (y : G) (z : G), x ◇ y = x ◇ ((y ◇ x) ◇ z) := by
  intros x y z;
  convert h x y x x x using 1;
  convert h _ _ _ _ _ using 1;
  rotate_left;
  exact x;
  exact x;
  exact x;
  grind

/-
Problem normal_0867: eq2197 → eq3304
-/
