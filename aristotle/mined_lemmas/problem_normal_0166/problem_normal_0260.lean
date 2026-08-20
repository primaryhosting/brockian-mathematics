import Mathlib.Tactic

class Magma (G : Type _) where op : G → G → G
set_option quotPrecheck false in
infixl:65 " ◇ " => Magma.op


-- Problem normal_0166: eq1359 → eq210

theorem problem_normal_0260 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G) (w : G), x = (y ◇ z) ◇ ((w ◇ x) ◇ z))
    : ∀ (x : G) (y : G) (z : G), x ◇ x = (y ◇ z) ◇ (x ◇ y) := by
  grind +suggestions

/-
Problem normal_0262: eq2621 → eq4442
-/
