import Mathlib.Tactic

class Magma (G : Type _) where op : G → G → G
set_option quotPrecheck false in
infixl:65 " ◇ " => Magma.op


-- Problem normal_0166: eq1359 → eq210

theorem problem_normal_0321 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G) (w : G), x = (((y ◇ y) ◇ z) ◇ w) ◇ x)
    : ∀ (x : G) (y : G) (z : G), x = (y ◇ (z ◇ y)) ◇ (y ◇ x) := by
  intro x y z
  have := h x (y ◇ y) z y
  grind

/-
Problem normal_0322: eq745 → eq1284
-/
