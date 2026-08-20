
import Mathlib.Tactic

set_option quotPrecheck false
class Magma (G : Type _) where op : G → G → G
infixl:65 " ◇ " => Magma.op

/-
Problem normal_0765: eq1708 → eq3230
-/

theorem problem_normal_0809 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G) (w : G), x = (y ◇ z) ◇ (x ◇ (w ◇ y)))
    : ∀ (x : G) (y : G) (z : G), x ◇ y = ((z ◇ x) ◇ x) ◇ y := by
  intro x y z;
  have h1 := h ( ‹Magma G›.op x y ) ( ‹Magma G›.op z x ) x y;
  grind

/-
Problem normal_0811: eq905 → eq2570
-/
