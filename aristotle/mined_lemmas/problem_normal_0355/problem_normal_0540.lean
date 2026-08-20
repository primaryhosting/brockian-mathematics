import Mathlib.Tactic

set_option quotPrecheck false
class Magma (G : Type _) where op : G → G → G
infixl:65 " ◇ " => Magma.op


-- Problem normal_0355: eq899 → eq4591

theorem problem_normal_0540 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G), x ◇ x = (y ◇ (z ◇ z)) ◇ z)
    : ∀ (x : G) (y : G), x ◇ x = (x ◇ (x ◇ x)) ◇ y := by
  intro x y
  have := h x y x; have := h y x x; have := h x x y
  have := h y y x; have := h x y y; have := h y x y
  have := h x x x; have := h y y y; grind

/-
Problem normal_0548: eq2198 → eq882
-/
