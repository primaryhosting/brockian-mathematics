import Mathlib.Tactic

set_option quotPrecheck false
class Magma (G : Type _) where op : G → G → G
infixl:65 " ◇ " => Magma.op


-- Problem normal_0355: eq899 → eq4591

theorem problem_normal_0571 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G) (w : G), x = ((y ◇ x) ◇ y) ◇ (z ◇ w))
    : ∀ (x : G) (y : G) (z : G), x ◇ (y ◇ z) = (y ◇ z) ◇ y := by
  have hxy : ∀ x y : G, x = y := by
    intro x y; rw [h x y y y, h y y y y]; grind
  intro x y z; exact hxy _ _

-- Problem normal_0576: eq3133 → eq2744
