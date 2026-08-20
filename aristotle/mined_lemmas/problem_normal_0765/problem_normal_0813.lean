
import Mathlib.Tactic

set_option quotPrecheck false
class Magma (G : Type _) where op : G → G → G
infixl:65 " ◇ " => Magma.op

/-
Problem normal_0765: eq1708 → eq3230
-/

theorem problem_normal_0813 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G), x = (y ◇ (y ◇ x)) ◇ (z ◇ y))
    : ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x = (((y ◇ z) ◇ w) ◇ y) ◇ u := by
  intro x y z w u;
  convert h _ _ _ using 1;
  congr! 1;
  convert h _ _ _ using 1;
  convert h _ _ _ using 1

/-
Problem normal_0816: eq2495 → eq4606
-/
