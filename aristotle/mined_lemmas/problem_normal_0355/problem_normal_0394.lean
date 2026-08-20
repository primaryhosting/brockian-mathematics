import Mathlib.Tactic

set_option quotPrecheck false
class Magma (G : Type _) where op : G → G → G
infixl:65 " ◇ " => Magma.op


-- Problem normal_0355: eq899 → eq4591

theorem problem_normal_0394 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G) (w : G), x = y ◇ (x ◇ (z ◇ (z ◇ w))))
    : ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = (z ◇ (w ◇ w)) ◇ y := by
  intro x y z w
  have := h x x x x; have := h y x x x
  have := h (x ◇ y) x x x; have := h ((z ◇ (w ◇ w)) ◇ y) x x x
  grind

/-
Problem normal_0400: eq591 → eq4398
-/
