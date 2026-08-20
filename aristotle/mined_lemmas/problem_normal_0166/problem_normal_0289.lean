import Mathlib.Tactic

class Magma (G : Type _) where op : G → G → G
set_option quotPrecheck false in
infixl:65 " ◇ " => Magma.op


-- Problem normal_0166: eq1359 → eq210

theorem problem_normal_0289 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G) (w : G), x = (y ◇ x) ◇ ((z ◇ w) ◇ z))
    : ∀ (x : G) (y : G), x ◇ y = (x ◇ x) ◇ x := by
  intro x y;
  have := h ( ‹Magma G›.op y y ) x y y;
  grind +suggestions

-- Problem normal_0292: eq3576 → eq3958
