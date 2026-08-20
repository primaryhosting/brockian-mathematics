import Mathlib.Tactic

set_option quotPrecheck false
class Magma (G : Type _) where op : G → G → G
infixl:65 " ◇ " => Magma.op


-- Problem normal_0355: eq899 → eq4591

theorem problem_normal_0362 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = (z ◇ w) ◇ w)
    : ∀ (x : G) (y : G) (z : G), (x ◇ y) ◇ y = (y ◇ x) ◇ z := by
  intro x y z; have := h x y y x; have := h (y ◇ x) z y x; grind

-- Problem normal_0363: eq2214 → eq667
