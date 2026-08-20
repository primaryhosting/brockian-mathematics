
import Mathlib.Tactic

set_option quotPrecheck false
class Magma (G : Type _) where op : G → G → G
infixl:65 " ◇ " => Magma.op

/-
Problem normal_0765: eq1708 → eq3230
-/

theorem problem_normal_0906 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G), x = ((y ◇ x) ◇ (x ◇ x)) ◇ z)
    : ∀ (x : G) (y : G) (z : G), x = y ◇ ((z ◇ x) ◇ (x ◇ y)) := by
  intro x y z;
  convert h x _ _ using 1;
  congr! 1;
  convert h y _ _ using 1;
  congr! 1;
  rotate_left 1;
  exact ( ‹Magma G›.op ( ‹Magma G›.op y x ) ( ‹Magma G›.op x x ) );
  exact ( ‹Magma G›.op ( ‹Magma G›.op ( ‹Magma G›.op y x ) ( ‹Magma G›.op x x ) ) y );
  grind +suggestions

/-
Problem normal_0910: eq2569 → eq442
-/
