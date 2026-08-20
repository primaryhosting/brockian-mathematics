import Mathlib.Tactic

set_option quotPrecheck false
class Magma (G : Type _) where op : G → G → G
infixl:65 " ◇ " => Magma.op


-- Problem normal_0355: eq899 → eq4591

theorem problem_normal_0385 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G) (w : G), x = (y ◇ x) ◇ (z ◇ (z ◇ w)))
    : ∀ (x : G) (y : G) (z : G), x = y ◇ ((z ◇ z) ◇ (y ◇ z)) := by
  intro x y z
  have := h x y z z; have := h (y ◇ x) y z z
  have := h (y ◇ (y ◇ x)) y z z; grind

/-
Problem normal_0390: eq700 → eq273
-/
