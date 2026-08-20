import Mathlib.Tactic

class Magma (G : Type _) where op : G → G → G
set_option quotPrecheck false in
infixl:65 " ◇ " => Magma.op


-- Problem normal_0166: eq1359 → eq210

theorem problem_normal_0263 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G), x = y ◇ (y ◇ (x ◇ (x ◇ z))))
    : ∀ (x : G) (y : G), x = ((y ◇ x) ◇ y) ◇ x := by
  grind +suggestions

/-
Problem normal_0268: eq220 → eq1169
-/
