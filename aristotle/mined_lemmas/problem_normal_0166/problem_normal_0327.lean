import Mathlib.Tactic

class Magma (G : Type _) where op : G → G → G
set_option quotPrecheck false in
infixl:65 " ◇ " => Magma.op


-- Problem normal_0166: eq1359 → eq210

theorem problem_normal_0327 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G) (w : G), x = (y ◇ (x ◇ (z ◇ w))) ◇ z)
    : ∀ (x : G) (y : G), x ◇ x = y ◇ ((y ◇ x) ◇ y) := by
  intro x y;
  have h1 := h x x x x;
  grind

/-
Problem normal_0328: eq2986 → eq1229
-/
