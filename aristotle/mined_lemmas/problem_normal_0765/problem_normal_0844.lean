
import Mathlib.Tactic

set_option quotPrecheck false
class Magma (G : Type _) where op : G → G → G
infixl:65 " ◇ " => Magma.op

/-
Problem normal_0765: eq1708 → eq3230
-/

theorem problem_normal_0844 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G) (w : G), x = (y ◇ (z ◇ x)) ◇ (w ◇ w))
    : ∀ (x : G) (y : G) (z : G), x = (x ◇ ((x ◇ x) ◇ y)) ◇ z := by
  intro x y z;
  convert h x x y z using 1;
  convert h _ _ _ _ using 1;
  congr! 1;
  convert h _ _ _ _ using 1;
  · exact x;
  · exact x

/-
Problem normal_0848: eq1495 → eq2212
-/
