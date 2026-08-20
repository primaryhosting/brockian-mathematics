import Mathlib.Tactic

class Magma (G : Type _) where op : G → G → G
set_option quotPrecheck false in
infixl:65 " ◇ " => Magma.op


-- Problem normal_0166: eq1359 → eq210

theorem problem_normal_0313 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G) (w : G), x = (y ◇ (z ◇ (x ◇ w))) ◇ z)
    : ∀ (x : G) (y : G) (z : G) (w : G), x = ((y ◇ x) ◇ (z ◇ z)) ◇ w := by
  intro x y z
  have h_all_eq : ∀ x y : G, x = y := by
    intro x y
    rw [h x y y x, h y x y x]
    grind
  exact fun w => h_all_eq _ _

/-
Problem normal_0314: eq1716 → eq4500
-/
