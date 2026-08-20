
import Mathlib.Tactic

set_option quotPrecheck false
class Magma (G : Type _) where op : G → G → G
infixl:65 " ◇ " => Magma.op

/-
Problem normal_0765: eq1708 → eq3230
-/

theorem problem_normal_0922 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G) (w : G), x = (y ◇ (x ◇ z)) ◇ (x ◇ w))
    : ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x = (x ◇ y) ◇ ((z ◇ w) ◇ u) := by
  intros x y z w u
  have := h x y z w;
  convert h x _ _ _ using 1;
  rotate_left;
  exact ( ‹Magma G›.op ( ‹Magma G›.op x y ) ( ‹Magma G›.op ( ‹Magma G›.op z w ) u ) );
  exact w;
  exact x ◇ x;
  grind

/-
Problem normal_0925: eq1771 → eq178
-/
