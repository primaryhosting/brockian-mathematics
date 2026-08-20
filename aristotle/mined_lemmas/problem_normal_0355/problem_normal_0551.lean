import Mathlib.Tactic

set_option quotPrecheck false
class Magma (G : Type _) where op : G → G → G
infixl:65 " ◇ " => Magma.op


-- Problem normal_0355: eq899 → eq4591

theorem problem_normal_0551 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G), x = y ◇ (x ◇ z))
    : ∀ (x : G) (y : G) (z : G), x = (y ◇ y) ◇ (y ◇ (x ◇ z)) := by
  intro x y z; have := h x (y ◇ y) z; have := h (x ◇ z) y z; grind

/-
Problem normal_0561: eq1147 → eq641
-/
