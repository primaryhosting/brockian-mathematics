
import Mathlib.Tactic

set_option quotPrecheck false
class Magma (G : Type _) where op : G → G → G
infixl:65 " ◇ " => Magma.op

/-
Problem normal_0765: eq1708 → eq3230
-/

theorem problem_normal_0768 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x = ((y ◇ x) ◇ (z ◇ w)) ◇ u)
    : ∀ (x : G) (y : G) (z : G), x ◇ y = z ◇ (y ◇ (z ◇ x)) := by
  intros x y z;
  convert h _ _ _ _ _ using 1;
  rotate_left;
  exact x;
  exact y;
  exact z;
  exact y;
  have := h x x x x x;
  grind

/-
Problem normal_0773: eq2603 → eq1845
-/
