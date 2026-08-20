import Mathlib.Tactic

class Magma (G : Type _) where op : G → G → G
set_option quotPrecheck false in
infixl:65 " ◇ " => Magma.op


-- Problem normal_0166: eq1359 → eq210

theorem problem_normal_0221 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G) (w : G), x = x ◇ (y ◇ (x ◇ (z ◇ w))))
    : ∀ (x : G) (y : G) (z : G), x = (x ◇ y) ◇ ((x ◇ z) ◇ y) := by
  intros x y z
  have := h x y z y;
  grind

-- Problem normal_0222: eq1107 → eq2016
