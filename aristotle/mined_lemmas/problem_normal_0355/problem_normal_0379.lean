import Mathlib.Tactic

set_option quotPrecheck false
class Magma (G : Type _) where op : G → G → G
infixl:65 " ◇ " => Magma.op


-- Problem normal_0355: eq899 → eq4591

theorem problem_normal_0379 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x ◇ (y ◇ z) = y ◇ (w ◇ u))
    : ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x ◇ (y ◇ y) = z ◇ (w ◇ u) := by
  grind

-- Problem normal_0382: eq1605 → eq1896
