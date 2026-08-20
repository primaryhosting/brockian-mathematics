import Mathlib.Tactic

class Magma (G : Type _) where op : G → G → G
set_option quotPrecheck false in
infixl:65 " ◇ " => Magma.op


-- Problem normal_0166: eq1359 → eq210

theorem problem_normal_0219 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G), x = y ◇ (x ◇ (y ◇ (x ◇ z))))
    : ∀ (x : G) (y : G) (z : G), x ◇ x = y ◇ (x ◇ (z ◇ y)) := by
  intro x y z
  have h1 := h x x x
  grind

/-
Problem normal_0221: eq435 → eq1651
-/
