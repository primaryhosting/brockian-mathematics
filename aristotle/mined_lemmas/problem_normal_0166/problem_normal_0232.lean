import Mathlib.Tactic

class Magma (G : Type _) where op : G → G → G
set_option quotPrecheck false in
infixl:65 " ◇ " => Magma.op


-- Problem normal_0166: eq1359 → eq210

theorem problem_normal_0232 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G), x = (y ◇ ((x ◇ z) ◇ y)) ◇ y)
    : ∀ (x : G) (y : G) (z : G) (w : G), x = (y ◇ (x ◇ z)) ◇ (x ◇ w) := by
  grind +splitIndPred

-- Problem normal_0235: eq1554 → eq413
