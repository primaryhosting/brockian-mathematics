
import Mathlib.Tactic

set_option quotPrecheck false
class Magma (G : Type _) where op : G → G → G
infixl:65 " ◇ " => Magma.op

/-
Problem normal_0765: eq1708 → eq3230
-/

theorem problem_normal_0864 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G) (w : G), x = ((y ◇ (z ◇ w)) ◇ x) ◇ w)
    : ∀ (x : G) (y : G) (z : G), x = (y ◇ (x ◇ (z ◇ x))) ◇ y := by
  have := h;
  convert this using 1;
  constructor <;> intro h y z;
  · exact?;
  · convert h y _ _ using 1;
    rotate_left;
    exact y;
    exact y;
    grind

/-
Problem normal_0866: eq4048 → eq3520
-/
