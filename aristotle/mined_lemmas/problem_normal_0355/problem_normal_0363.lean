import Mathlib.Tactic

set_option quotPrecheck false
class Magma (G : Type _) where op : G → G → G
infixl:65 " ◇ " => Magma.op


-- Problem normal_0355: eq899 → eq4591

theorem problem_normal_0363 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G) (w : G), x = ((y ◇ z) ◇ w) ◇ (x ◇ z))
    : ∀ (x : G) (y : G), x = y ◇ (x ◇ ((x ◇ x) ◇ y)) := by
  intro x y
  have := h x (x ◇ x) x (x ◇ x)
  have := h (x ◇ x) y (x ◇ x) (x ◇ x)
  grind

/-
Problem normal_0365: eq1351 → eq2461
-/
