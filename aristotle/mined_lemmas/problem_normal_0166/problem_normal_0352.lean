import Mathlib.Tactic

class Magma (G : Type _) where op : G → G → G
set_option quotPrecheck false in
infixl:65 " ◇ " => Magma.op


-- Problem normal_0166: eq1359 → eq210

theorem problem_normal_0352 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G), x = ((y ◇ y) ◇ (x ◇ y)) ◇ z)
    : ∀ (x : G) (y : G), x = (x ◇ y) ◇ (y ◇ x) := by
  grind +suggestions
