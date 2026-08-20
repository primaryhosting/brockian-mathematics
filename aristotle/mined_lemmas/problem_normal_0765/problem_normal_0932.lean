
import Mathlib.Tactic

set_option quotPrecheck false
class Magma (G : Type _) where op : G → G → G
infixl:65 " ◇ " => Magma.op

/-
Problem normal_0765: eq1708 → eq3230
-/

theorem problem_normal_0932 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G), x = y ◇ ((x ◇ x) ◇ z))
    : ∀ (x : G) (y : G) (z : G) (w : G), x = (((y ◇ z) ◇ x) ◇ w) ◇ y := by
  intro x y z w;
  convert h x _ _ using 1;
  congr! 1;
  convert h y _ _ using 1;
  exact x

/-
Problem normal_0934: eq3382 → eq3482
-/
