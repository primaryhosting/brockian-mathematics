import Mathlib.Tactic

set_option quotPrecheck false
class Magma (G : Type _) where op : G → G → G
infixl:65 " ◇ " => Magma.op


-- Problem normal_0355: eq899 → eq4591

theorem problem_normal_0463 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G) (w : G), x = ((y ◇ (z ◇ x)) ◇ w) ◇ w)
    : ∀ (x : G) (y : G) (z : G) (w : G), x = y ◇ (((z ◇ w) ◇ w) ◇ y) := by
  intro x y;
  rw [ h x y y y, h y y y y ];
  grind

/-
Problem normal_0465: eq794 → eq1626
-/
