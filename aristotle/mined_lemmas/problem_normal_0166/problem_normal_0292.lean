import Mathlib.Tactic

class Magma (G : Type _) where op : G → G → G
set_option quotPrecheck false in
infixl:65 " ◇ " => Magma.op


-- Problem normal_0166: eq1359 → eq210

theorem problem_normal_0292 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = y ◇ ((z ◇ z) ◇ w))
    : ∀ (x : G) (y : G) (z : G), x ◇ y = (y ◇ (x ◇ z)) ◇ y := by
  intro x y z
  have := h x y z z
  grind

-- Problem normal_0300: eq2579 → eq2212
