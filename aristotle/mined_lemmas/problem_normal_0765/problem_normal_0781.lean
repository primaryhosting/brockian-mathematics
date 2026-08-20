
import Mathlib.Tactic

set_option quotPrecheck false
class Magma (G : Type _) where op : G → G → G
infixl:65 " ◇ " => Magma.op

/-
Problem normal_0765: eq1708 → eq3230
-/

theorem problem_normal_0781 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x = y ◇ (z ◇ ((w ◇ u) ◇ x)))
    : ∀ (x : G) (y : G) (z : G), (x ◇ y) ◇ x = (z ◇ x) ◇ x := by
  -- Let's assume there exists an element $k$ such that $k ◇ k = k$.
  by_contra h_contra;
  refine' h_contra fun x y z => _;
  convert h _ _ _ _ _ using 1;
  rotate_left 1;
  exact z;
  exact x;
  exact x;
  exact x;
  grind

/-
Problem normal_0784: eq3129 → eq4082
-/
