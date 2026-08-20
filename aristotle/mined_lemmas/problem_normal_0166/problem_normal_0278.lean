import Mathlib.Tactic

class Magma (G : Type _) where op : G → G → G
set_option quotPrecheck false in
infixl:65 " ◇ " => Magma.op


-- Problem normal_0166: eq1359 → eq210

theorem problem_normal_0278 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G) (w : G), x = (((y ◇ x) ◇ z) ◇ x) ◇ w)
    : ∀ (x : G) (y : G) (z : G) (w : G), x = y ◇ (z ◇ (z ◇ (w ◇ x))) := by
  intro x y z w
  have := h x x x x
  have := h y x x x
  grind

/-
Problem normal_0282: eq1269 → eq3875
-/
