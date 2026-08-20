
import Mathlib.Tactic

set_option quotPrecheck false
class Magma (G : Type _) where op : G → G → G
infixl:65 " ◇ " => Magma.op

/-
Problem normal_0765: eq1708 → eq3230
-/

theorem problem_normal_0820 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G), x = y ◇ (x ◇ ((y ◇ x) ◇ z)))
    : ∀ (x : G) (y : G) (z : G), x = (y ◇ ((x ◇ z) ◇ x)) ◇ x := by
  have := h;
  convert this using 1;
  constructor <;> intro h y z;
  · grind;
  · convert h _ _ using 1;
    rotate_left 1;
    exact y;
    exact ‹Magma G›.op ( ‹Magma G›.op y ( ‹Magma G›.op ( ‹Magma G›.op ‹_› z ) ‹_› ) ) ‹_›;
    grind

/-
Problem normal_0823: eq2380 → eq4422
-/
