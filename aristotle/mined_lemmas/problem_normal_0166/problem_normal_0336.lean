import Mathlib.Tactic

class Magma (G : Type _) where op : G → G → G
set_option quotPrecheck false in
infixl:65 " ◇ " => Magma.op


-- Problem normal_0166: eq1359 → eq210

theorem problem_normal_0336 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x = ((y ◇ z) ◇ (w ◇ x)) ◇ u)
    : ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = (z ◇ (x ◇ y)) ◇ w := by
  intro x y z
  have := h (x ◇ y) x y z
  intro w
  have := this (x ◇ y)
  grind

-- Problem normal_0342: eq1321 → eq2805
