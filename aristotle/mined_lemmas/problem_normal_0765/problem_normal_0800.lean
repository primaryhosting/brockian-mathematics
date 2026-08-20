
import Mathlib.Tactic

set_option quotPrecheck false
class Magma (G : Type _) where op : G → G → G
infixl:65 " ◇ " => Magma.op

/-
Problem normal_0765: eq1708 → eq3230
-/

theorem problem_normal_0800 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G), x ◇ y = (z ◇ z) ◇ (x ◇ x))
    : ∀ (x : G) (y : G) (z : G), x ◇ y = (y ◇ (x ◇ z)) ◇ x := by
  have := h;
  convert this using 1;
  constructor <;> intro h y z <;> have := h y z <;> have := this.symm <;> simp_all +decide;
  · solve_by_elim;
  · grind

/-
Problem normal_0802: eq3171 → eq2909
-/
