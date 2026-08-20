import Mathlib.Tactic

class Magma (G : Type _) where op : G → G → G
set_option quotPrecheck false in
infixl:65 " ◇ " => Magma.op


-- Problem normal_0166: eq1359 → eq210

theorem problem_normal_0177 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = z ◇ ((w ◇ y) ◇ z))
    : ∀ (x : G) (y : G) (z : G), x ◇ y = x ◇ (y ◇ (z ◇ z)) := by
  intro x y z
  have h1 := h x y x y
  have h2 := h x y y (z ◇ z)
  grind

-- Problem normal_0187: eq1268 → eq1426
