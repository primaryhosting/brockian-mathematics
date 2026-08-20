
import Mathlib.Tactic

set_option quotPrecheck false
class Magma (G : Type _) where op : G → G → G
infixl:65 " ◇ " => Magma.op

/-
Problem normal_0765: eq1708 → eq3230
-/

theorem problem_normal_0940 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x = y ◇ (z ◇ (x ◇ (w ◇ u))))
    : ∀ (x : G) (y : G) (z : G), x ◇ x = (y ◇ z) ◇ (z ◇ x) := by
  -- From h x x x x x: x = x ◇ (x ◇ (x ◇ (x ◇ x))). The RHS of h is insensitive to y and z and w and u in some sense.
  intros x y z
  have h1 := h x x x x x;
  grind

/-
Problem normal_0941: eq1766 → eq317
-/
