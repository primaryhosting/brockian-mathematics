import Mathlib.Tactic

class Magma (G : Type _) where op : G → G → G
set_option quotPrecheck false in
infixl:65 " ◇ " => Magma.op


-- Problem normal_0166: eq1359 → eq210

theorem problem_normal_0328 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G) (w : G), x = ((y ◇ (z ◇ x)) ◇ w) ◇ y)
    : ∀ (x : G) (y : G), x = x ◇ (((x ◇ y) ◇ x) ◇ y) := by
  intro x y
  have h1 := h x x x x
  have h2 := h x y x y
  grind

/-
Problem normal_0329: eq1605 → eq2627
-/
