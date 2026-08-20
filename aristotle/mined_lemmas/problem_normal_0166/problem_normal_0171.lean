import Mathlib.Tactic

class Magma (G : Type _) where op : G → G → G
set_option quotPrecheck false in
infixl:65 " ◇ " => Magma.op


-- Problem normal_0166: eq1359 → eq210

theorem problem_normal_0171 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = z ◇ (y ◇ (x ◇ w)))
    : ∀ (x : G) (y : G), x ◇ y = (x ◇ x) ◇ (y ◇ x) := by
  intro x y
  have h1 := h x y x x
  have h2 := h x x y x
  have h3 := h x x x x
  grind

-- Problem normal_0177: eq3640 → eq3323
