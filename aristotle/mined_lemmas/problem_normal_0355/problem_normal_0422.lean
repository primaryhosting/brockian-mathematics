import Mathlib.Tactic

set_option quotPrecheck false
class Magma (G : Type _) where op : G → G → G
infixl:65 " ◇ " => Magma.op


-- Problem normal_0355: eq899 → eq4591

theorem problem_normal_0422 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G), x = ((y ◇ z) ◇ x) ◇ (z ◇ y))
    : ∀ (x : G) (y : G) (z : G), (x ◇ y) ◇ x = (y ◇ z) ◇ z := by
  grind

-- Problem normal_0430: eq1511 → eq270
