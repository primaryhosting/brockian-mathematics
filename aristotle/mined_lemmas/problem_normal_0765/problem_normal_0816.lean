
import Mathlib.Tactic

set_option quotPrecheck false
class Magma (G : Type _) where op : G → G → G
infixl:65 " ◇ " => Magma.op

/-
Problem normal_0765: eq1708 → eq3230
-/

theorem problem_normal_0816 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G), x = (y ◇ ((x ◇ x) ◇ x)) ◇ z)
    : ∀ (x : G) (y : G), (x ◇ x) ◇ y = (y ◇ x) ◇ y := by
  revert h;
  intro h y;
  convert h y _ _ using 1;
  rotate_left;
  exact y ◇ y;
  exact ( ‹Magma G›.op ( ‹Magma G›.op y y ) y );
  grind

/-
Problem normal_0818: eq2376 → eq307
-/
