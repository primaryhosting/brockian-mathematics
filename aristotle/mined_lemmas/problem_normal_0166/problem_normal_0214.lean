import Mathlib.Tactic

class Magma (G : Type _) where op : G → G → G
set_option quotPrecheck false in
infixl:65 " ◇ " => Magma.op


-- Problem normal_0166: eq1359 → eq210

theorem problem_normal_0214 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G), x = (y ◇ ((z ◇ x) ◇ x)) ◇ y)
    : ∀ (x : G) (y : G) (z : G), x = ((y ◇ y) ◇ (z ◇ x)) ◇ y := by
  intros x y z
  have hx := h x y z
  have hy := h y z x
  have hz := h z x y;
  convert h x y z using 1;
  congr! 1;
  convert h _ _ _ using 1;
  rotate_left 1;
  exact y;
  exact y;
  convert h _ _ _ using 1;
  rotate_left;
  exact y;
  exact (x ◇ x);
  grind

-- Problem normal_0219: eq475 → eq3275
