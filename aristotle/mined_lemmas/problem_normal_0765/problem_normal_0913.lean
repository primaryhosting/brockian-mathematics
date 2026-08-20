
import Mathlib.Tactic

set_option quotPrecheck false
class Magma (G : Type _) where op : G → G → G
infixl:65 " ◇ " => Magma.op

/-
Problem normal_0765: eq1708 → eq3230
-/

theorem problem_normal_0913 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G) (w : G), x = ((y ◇ (z ◇ x)) ◇ x) ◇ w)
    : ∀ (x : G) (y : G) (z : G), (x ◇ y) ◇ x = (z ◇ y) ◇ y := by
  intro x y z;
  convert h _ _ _ _;
  convert h _ _ _ _;
  · exact x;
  · exact x;
  · convert h y _ _ _;
    convert h x _ _ _;
    · exact x;
    · exact x;
    · exact x;
  · exact x

/-
Problem normal_0917: eq1164 → eq4660
-/
