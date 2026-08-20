import Mathlib.Tactic

set_option quotPrecheck false
class Magma (G : Type _) where op : G → G → G
infixl:65 " ◇ " => Magma.op


-- Problem normal_0355: eq899 → eq4591

theorem problem_normal_0522 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G), x = (y ◇ y) ◇ (y ◇ (z ◇ x)))
    : ∀ (x : G) (y : G), x ◇ y = (y ◇ y) ◇ y := by
  grind

-- Problem normal_0540: eq3907 → eq3863
