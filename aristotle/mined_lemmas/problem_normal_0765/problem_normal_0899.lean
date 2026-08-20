
import Mathlib.Tactic

set_option quotPrecheck false
class Magma (G : Type _) where op : G → G → G
infixl:65 " ◇ " => Magma.op

/-
Problem normal_0765: eq1708 → eq3230
-/

theorem problem_normal_0899 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G) (w : G), x = y ◇ (z ◇ (x ◇ (w ◇ y))))
    : ∀ (x : G) (y : G) (z : G), x = ((y ◇ (y ◇ z)) ◇ z) ◇ y := by
  intro x y z;
  convert h x _ _ _ using 1;
  congr! 1;
  convert h y _ _ _

/-
Problem normal_0906: eq2698 → eq944
-/
