
import Mathlib.Tactic

set_option quotPrecheck false
class Magma (G : Type _) where op : G → G → G
infixl:65 " ◇ " => Magma.op

/-
Problem normal_0765: eq1708 → eq3230
-/

theorem problem_normal_0802 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G) (w : G), x = (((y ◇ y) ◇ z) ◇ w) ◇ x)
    : ∀ (x : G) (y : G), x = ((y ◇ (x ◇ y)) ◇ x) ◇ x := by
  -- Apply the given hypothesis `h` to rewrite the goal in terms of `◇` operations.
  have := h;
  convert this using 1;
  constructor <;> intro h;
  · grind +extAll;
  · intro y;
    have := h y ( ‹Magma G›.op y y ) ( ‹Magma G›.op y y );
    grind

/-
Problem normal_0809: eq1565 → eq4192
-/
