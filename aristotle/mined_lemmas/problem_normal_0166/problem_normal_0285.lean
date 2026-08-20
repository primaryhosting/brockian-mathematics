import Mathlib.Tactic

class Magma (G : Type _) where op : G → G → G
set_option quotPrecheck false in
infixl:65 " ◇ " => Magma.op


-- Problem normal_0166: eq1359 → eq210

theorem problem_normal_0285 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G), x = (y ◇ (x ◇ z)) ◇ (y ◇ y))
    : ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = (z ◇ (x ◇ w)) ◇ w := by
  grind +suggestions

/-
Problem normal_0287: eq2775 → eq3943
-/
