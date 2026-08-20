
import Mathlib.Tactic

set_option quotPrecheck false
class Magma (G : Type _) where op : G → G → G
infixl:65 " ◇ " => Magma.op

/-
Problem normal_0765: eq1708 → eq3230
-/

theorem problem_normal_0891 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x = ((y ◇ z) ◇ x) ◇ (w ◇ u))
    : ∀ (x : G) (y : G) (z : G), x ◇ y = z ◇ (z ◇ (y ◇ y)) := by
  intro x y z;
  convert h _ _ _ _ _ using 1;
  rotate_left;
  exact z;
  exact y;
  exact x ◇ x;
  exact y;
  grind +suggestions

/-
Problem normal_0896: eq544 → eq2279
-/
