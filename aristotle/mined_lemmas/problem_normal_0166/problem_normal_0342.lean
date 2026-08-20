import Mathlib.Tactic

class Magma (G : Type _) where op : G → G → G
set_option quotPrecheck false in
infixl:65 " ◇ " => Magma.op


-- Problem normal_0166: eq1359 → eq210

theorem problem_normal_0342 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G) (w : G), x = y ◇ (((y ◇ x) ◇ z) ◇ w))
    : ∀ (x : G) (y : G) (z : G), x = ((y ◇ z) ◇ (z ◇ x)) ◇ y := by
  intro x y z
  have := h x y z x
  have := h x x x x
  grind

/-
Problem normal_0346: eq3109 → eq450
-/
