import Mathlib.Tactic

set_option quotPrecheck false
class Magma (G : Type _) where op : G → G → G
infixl:65 " ◇ " => Magma.op


-- Problem normal_0355: eq899 → eq4591

theorem problem_normal_0401 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G) (w : G), x = (y ◇ ((x ◇ z) ◇ x)) ◇ w)
    : ∀ (x : G) (y : G) (z : G), x ◇ y = y ◇ (y ◇ (z ◇ z)) := by
  intro x y z; rw [h x y y y, h y y y y]; grind

/-
Problem normal_0404: eq1499 → eq3250
-/
