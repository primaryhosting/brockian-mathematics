import Mathlib.Tactic

set_option quotPrecheck false
class Magma (G : Type _) where op : G → G → G
infixl:65 " ◇ " => Magma.op


-- Problem normal_0355: eq899 → eq4591

theorem problem_normal_0430 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G) (w : G), x = (y ◇ x) ◇ (z ◇ (w ◇ y)))
    : ∀ (x : G) (y : G), x = ((y ◇ x) ◇ x) ◇ x := by
  intro x y; have := h x y x x; have := h x x x x
  have := h x (y ◇ x) x x; have := h x y x y; grind

/-
Problem normal_0433: eq4219 → eq3771
-/
