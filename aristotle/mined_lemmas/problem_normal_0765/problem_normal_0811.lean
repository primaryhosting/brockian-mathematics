
import Mathlib.Tactic

set_option quotPrecheck false
class Magma (G : Type _) where op : G → G → G
infixl:65 " ◇ " => Magma.op

/-
Problem normal_0765: eq1708 → eq3230
-/

theorem problem_normal_0811 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x = y ◇ ((x ◇ z) ◇ (w ◇ u)))
    : ∀ (x : G) (y : G) (z : G) (w : G), x = (y ◇ ((z ◇ x) ◇ x)) ◇ w := by
  intro x y z;
  convert h x _ _ _ _ using 1;
  rotate_left;
  exact y;
  exact z;
  exact x;
  exact z;
  constructor;
  · grind;
  · intro hx w;
    convert h x _ _ _ _ using 1;
    rotate_left;
    bv_omega;
    exact x;
    exact x;
    exact x;
    grind

/-
Problem normal_0813: eq1928 → eq3236
-/
