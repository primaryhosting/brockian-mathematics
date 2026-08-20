import Mathlib.Tactic

class Magma (G : Type _) where op : G → G → G
set_option quotPrecheck false in
infixl:65 " ◇ " => Magma.op


-- Problem normal_0166: eq1359 → eq210

theorem problem_normal_0317 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G) (w : G), x = ((y ◇ x) ◇ (y ◇ z)) ◇ w)
    : ∀ (x : G) (y : G), x = (x ◇ x) ◇ ((x ◇ x) ◇ y) := by
  intro x y
  have := h x x x y;
  grind

-- Problem normal_0321: eq3171 → eq1979
