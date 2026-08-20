
import Mathlib.Tactic

set_option quotPrecheck false
class Magma (G : Type _) where op : G → G → G
infixl:65 " ◇ " => Magma.op

/-
Problem normal_0765: eq1708 → eq3230
-/

theorem problem_normal_0851 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G), x = (y ◇ ((x ◇ x) ◇ x)) ◇ z)
    : ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = (z ◇ w) ◇ (w ◇ w) := by
  intros x y z w;
  convert h _ _ _ using 1;
  congr! 1;
  convert h _ _ _ using 1;
  exact x

/-
Problem normal_0861: eq2604 → eq2863
-/
