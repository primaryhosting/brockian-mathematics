
import Mathlib.Tactic

set_option quotPrecheck false
class Magma (G : Type _) where op : G → G → G
infixl:65 " ◇ " => Magma.op

/-
Problem normal_0765: eq1708 → eq3230
-/

theorem problem_normal_0773 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G), x = (y ◇ ((z ◇ z) ◇ x)) ◇ z)
    : ∀ (x : G) (y : G) (z : G), x = (x ◇ (x ◇ y)) ◇ (z ◇ z) := by
  intro x y z;
  convert h _ _ _ using 1;
  congr! 1;
  convert h _ _ _ using 1;
  exact x

/-
Problem normal_0781: eq811 → eq4642
-/
