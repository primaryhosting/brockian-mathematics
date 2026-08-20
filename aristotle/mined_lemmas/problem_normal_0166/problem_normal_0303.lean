import Mathlib.Tactic

class Magma (G : Type _) where op : G → G → G
set_option quotPrecheck false in
infixl:65 " ◇ " => Magma.op


-- Problem normal_0166: eq1359 → eq210

theorem problem_normal_0303 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G), x = (y ◇ (z ◇ x)) ◇ z)
    : ∀ (x : G) (y : G) (z : G), x = y ◇ (((z ◇ x) ◇ x) ◇ y) := by
  grind +revert

-- Problem normal_0313: eq2378 → eq2727
