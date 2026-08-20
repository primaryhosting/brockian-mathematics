import Mathlib.Tactic

set_option quotPrecheck false
class Magma (G : Type _) where op : G → G → G
infixl:65 " ◇ " => Magma.op


-- Problem normal_0355: eq899 → eq4591

theorem problem_normal_0500 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G) (w : G), x = ((y ◇ z) ◇ w) ◇ (x ◇ w))
    : ∀ (x : G) (y : G) (z : G), x ◇ y = z ◇ ((z ◇ y) ◇ z) := by
  have h_eq := fun x y => h x y y y; grind

/-
Problem normal_0504: eq3834 → eq3864
-/
