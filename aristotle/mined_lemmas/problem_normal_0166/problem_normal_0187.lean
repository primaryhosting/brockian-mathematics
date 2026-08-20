import Mathlib.Tactic

class Magma (G : Type _) where op : G → G → G
set_option quotPrecheck false in
infixl:65 " ◇ " => Magma.op


-- Problem normal_0166: eq1359 → eq210

theorem problem_normal_0187 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G), x = x ◇ (((y ◇ z) ◇ z) ◇ z))
    : ∀ (x : G), x = (x ◇ x) ◇ (x ◇ (x ◇ x)) := by
  intro x
  have h1 := h x x x
  have h2 := h (x ◇ x) x x
  grind

-- Problem normal_0188: eq3767 → eq4431
