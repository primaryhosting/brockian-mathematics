
import Mathlib.Tactic

set_option quotPrecheck false
class Magma (G : Type _) where op : G → G → G
infixl:65 " ◇ " => Magma.op

/-
Problem normal_0765: eq1708 → eq3230
-/

theorem problem_normal_0861 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G) (w : G), x = (y ◇ ((z ◇ z) ◇ x)) ◇ w)
    : ∀ (x : G) (y : G), x = ((x ◇ (y ◇ x)) ◇ x) ◇ y := by
  intro x y;
  convert h x _ _ _;
  convert h x _ _ _;
  exact x

/-
Problem normal_0864: eq3027 → eq2311
-/
