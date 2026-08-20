import Mathlib.Tactic

set_option quotPrecheck false
class Magma (G : Type _) where op : G → G → G
infixl:65 " ◇ " => Magma.op


-- Problem normal_0355: eq899 → eq4591

theorem problem_normal_0471 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G) (w : G), x = ((y ◇ z) ◇ w) ◇ (x ◇ w))
    : ∀ (x : G) (y : G) (z : G), x = x ◇ (y ◇ (y ◇ (z ◇ y))) := by
  intro x y z;
  -- Apply the hypothesis `h` with `x = x`, `y = y`, `z = y`, and `w = z`.
  have := h x y y y;
  have := h x y z y;
  have := h y x x y;
  have := h y x y x;
  have := h y y x y;
  have := h y y y x;
  grind;

-- Problem normal_0474: eq291 → eq1480
