import Mathlib.Tactic

class Magma (G : Type _) where op : G → G → G
set_option quotPrecheck false in
infixl:65 " ◇ " => Magma.op


-- Problem normal_0166: eq1359 → eq210

theorem problem_normal_0346 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G), x = (((y ◇ x) ◇ x) ◇ z) ◇ y)
    : ∀ (x : G) (y : G) (z : G), x = x ◇ (y ◇ (z ◇ (y ◇ x))) := by
  intro x y z;
  have h1 := h x x x;
  grind

/-
Problem normal_0352: eq2738 → eq159
-/
