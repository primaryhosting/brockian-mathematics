import Mathlib.Tactic

set_option quotPrecheck false
class Magma (G : Type _) where op : G → G → G
infixl:65 " ◇ " => Magma.op


-- Problem normal_0355: eq899 → eq4591

theorem problem_normal_0476 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G), x = (y ◇ y) ◇ ((z ◇ x) ◇ y))
    : ∀ (x : G) (y : G), x ◇ x = (y ◇ (y ◇ x)) ◇ y := by
  grind

/-
Problem normal_0480: eq884 → eq3695
-/
