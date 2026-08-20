import Mathlib.Tactic

set_option quotPrecheck false
class Magma (G : Type _) where op : G → G → G
infixl:65 " ◇ " => Magma.op


-- Problem normal_0355: eq899 → eq4591

theorem problem_normal_0491 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G), x = (y ◇ x) ◇ ((x ◇ z) ◇ y))
    : ∀ (x : G) (y : G) (z : G) (w : G), x = (((x ◇ y) ◇ z) ◇ w) ◇ w := by
  grind

/-
Problem normal_0492: eq691 → eq2038
-/
