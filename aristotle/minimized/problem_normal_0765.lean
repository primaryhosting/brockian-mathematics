
import Mathlib.Tactic

set_option quotPrecheck false
class Magma (G : Type _) where op : G → G → G
infixl:65 " ◇ " => Magma.op

/-
Problem normal_0765: eq1708 → eq3230
-/

theorem problem_normal_0765 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G) (w : G), x = (y ◇ x) ◇ ((z ◇ y) ◇ w))
    : ∀ (x : G) (y : G) (z : G) (w : G), x = (((y ◇ z) ◇ w) ◇ x) ◇ w := by
  intro x y z w;
  have := h x y z w;
  convert h x _ _ _ using 1;
  rotate_left 1;
  exact ( ‹Magma G›.op ( ‹Magma G›.op y z ) w );
  bv_omega;
  exact ( ‹Magma G›.op ( ‹Magma G›.op y z ) w );
  congr! 1;
  convert h w _ _ _ using 1;
  rotate_left;
  exact ‹Magma G›.op y z;
  exact w;
  exact w;
  grind

/-
Problem normal_0768: eq2732 → eq3404
-/
