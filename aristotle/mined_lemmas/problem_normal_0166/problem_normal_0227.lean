import Mathlib.Tactic

class Magma (G : Type _) where op : G → G → G
set_option quotPrecheck false in
infixl:65 " ◇ " => Magma.op


-- Problem normal_0166: eq1359 → eq210

theorem problem_normal_0227 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G) (w : G), x = (y ◇ (z ◇ (x ◇ w))) ◇ y)
    : ∀ (x : G) (y : G) (z : G), x = y ◇ ((y ◇ (z ◇ z)) ◇ z) := by
  intro x y z
  have h1 := h x y z z
  have h2 := h y y z z
  have h3 := h x y z x
  grind

-- Problem normal_0232: eq2518 → eq1907
