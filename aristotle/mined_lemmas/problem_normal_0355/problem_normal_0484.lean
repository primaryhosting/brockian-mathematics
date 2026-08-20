import Mathlib.Tactic

set_option quotPrecheck false
class Magma (G : Type _) where op : G → G → G
infixl:65 " ◇ " => Magma.op


-- Problem normal_0355: eq899 → eq4591

theorem problem_normal_0484 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G), x = ((y ◇ z) ◇ (y ◇ x)) ◇ y)
    : ∀ (x : G) (y : G) (z : G) (w : G), x = ((y ◇ (z ◇ w)) ◇ y) ◇ y := by
  have := h;
  convert this using 1;
  grind +extAll

-- Problem normal_0491: eq1688 → eq3100
