
import Mathlib.Tactic

set_option quotPrecheck false
class Magma (G : Type _) where op : G → G → G
infixl:65 " ◇ " => Magma.op

/-
Problem normal_0765: eq1708 → eq3230
-/

theorem problem_normal_0949 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G) (w : G), x = y ◇ ((x ◇ z) ◇ (x ◇ w)))
    : ∀ (x : G) (y : G) (z : G) (w : G), x = (y ◇ z) ◇ ((w ◇ z) ◇ z) := by
  intro x y z w;
  convert h x _ _ _ using 1;
  rotate_left;
  exact ( ‹Magma G›.op ( ‹Magma G›.op y z ) ( ‹Magma G›.op ( ‹Magma G›.op w z ) z ) );
  exact x ◇ x;
  exact x;
  grind

/-
Problem normal_0954: eq3985 → eq3277
-/
