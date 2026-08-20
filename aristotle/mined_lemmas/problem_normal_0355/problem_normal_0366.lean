import Mathlib.Tactic

set_option quotPrecheck false
class Magma (G : Type _) where op : G → G → G
infixl:65 " ◇ " => Magma.op


-- Problem normal_0355: eq899 → eq4591

theorem problem_normal_0366 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G) (w : G), x = (y ◇ (x ◇ z)) ◇ (w ◇ w))
    : ∀ (x : G) (y : G) (z : G), x ◇ y = ((z ◇ z) ◇ z) ◇ x := by
  have h_all_eq : ∀ x y : G, x = y := by
    intro x y; have h1 := h x y x x; have h2 := h y x y y; grind
  intro x y z; exact h_all_eq _ _

-- Problem normal_0379: eq4368 → eq4356
