import Mathlib.Tactic

set_option quotPrecheck false
class Magma (G : Type _) where op : G → G → G
infixl:65 " ◇ " => Magma.op


-- Problem normal_0355: eq899 → eq4591

theorem problem_normal_0576 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G) (w : G), x = (((y ◇ x) ◇ z) ◇ z) ◇ w)
    : ∀ (x : G) (y : G), x = ((y ◇ y) ◇ (y ◇ x)) ◇ y := by
  intro x y; have := h x y y y; have := h y x x x; have := h x x y y; grind

/-
Problem normal_0578: eq3395 → eq3745
-/
