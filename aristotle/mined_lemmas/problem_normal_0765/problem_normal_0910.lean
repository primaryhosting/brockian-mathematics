
import Mathlib.Tactic

set_option quotPrecheck false
class Magma (G : Type _) where op : G → G → G
infixl:65 " ◇ " => Magma.op

/-
Problem normal_0765: eq1708 → eq3230
-/

theorem problem_normal_0910 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G), x = (y ◇ ((z ◇ x) ◇ x)) ◇ z)
    : ∀ (x : G) (y : G) (z : G), x = x ◇ (y ◇ (y ◇ (z ◇ x))) := by
  have := h;
  convert this using 1;
  constructor <;> intro h y z;
  · exact this _ _ _;
  · convert h _ _ using 1;
    congr! 1;
    convert h _ _ using 1;
    exact y

/-
Problem normal_0913: eq2976 → eq4646
-/
