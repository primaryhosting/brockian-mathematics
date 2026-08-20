import Mathlib.Tactic

set_option quotPrecheck false
class Magma (G : Type _) where op : G → G → G
infixl:65 " ◇ " => Magma.op


-- Problem normal_0355: eq899 → eq4591

theorem problem_normal_0567 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x = y ◇ (z ◇ ((x ◇ w) ◇ u)))
    : ∀ (x : G) (y : G) (z : G), x = (x ◇ (y ◇ y)) ◇ z := by
  intro x y z; have := h x x z x x; grind

-- Problem normal_0571: eq2106 → eq4532
