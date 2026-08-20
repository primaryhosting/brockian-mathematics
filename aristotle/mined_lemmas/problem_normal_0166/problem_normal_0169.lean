import Mathlib.Tactic

class Magma (G : Type _) where op : G → G → G
set_option quotPrecheck false in
infixl:65 " ◇ " => Magma.op


-- Problem normal_0166: eq1359 → eq210

theorem problem_normal_0169 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G) (w : G), x = ((y ◇ z) ◇ (x ◇ z)) ◇ w)
    : ∀ (x : G) (y : G) (z : G), x = ((y ◇ y) ◇ (z ◇ y)) ◇ y := by
  intro x y z
  have h1 := h x y y y
  have h2 := h y z y y
  grind

-- Problem normal_0171: eq3399 → eq3714
