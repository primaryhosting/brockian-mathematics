import Mathlib.Tactic

set_option quotPrecheck false
class Magma (G : Type _) where op : G → G → G
infixl:65 " ◇ " => Magma.op


-- Problem normal_0355: eq899 → eq4591

theorem problem_normal_0460 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G), x = (((y ◇ x) ◇ z) ◇ y) ◇ x)
    : ∀ (x : G) (y : G), x ◇ y = (y ◇ (y ◇ x)) ◇ y := by
  intro x y; have := h x y x; have := h y x y; have := h (x ◇ y) x y
  have := h (x ◇ y) y x; grind

/-
Problem normal_0461: eq2569 → eq866
-/
