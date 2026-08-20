import Mathlib.Tactic

set_option quotPrecheck false
class Magma (G : Type _) where op : G → G → G
infixl:65 " ◇ " => Magma.op


-- Problem normal_0355: eq899 → eq4591

theorem problem_normal_0461 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G), x = (y ◇ ((z ◇ x) ◇ x)) ◇ z)
    : ∀ (x : G) (y : G) (z : G) (w : G), x = x ◇ ((y ◇ z) ◇ (w ◇ z)) := by
  intro x y z;
  intros w;
  convert h x _ _ using 1;
  congr! 1;
  convert h x _ _ using 1;
  exact x

/-
Problem normal_0463: eq2988 → eq1416
-/
