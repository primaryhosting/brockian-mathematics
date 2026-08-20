
import Mathlib.Tactic

set_option quotPrecheck false
class Magma (G : Type _) where op : G → G → G
infixl:65 " ◇ " => Magma.op

/-
Problem normal_0765: eq1708 → eq3230
-/

theorem problem_normal_0848 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G), x = (y ◇ x) ◇ (y ◇ (z ◇ y)))
    : ∀ (x : G) (y : G) (z : G) (w : G), x = ((y ◇ z) ◇ w) ◇ (x ◇ x) := by
  intro x;
  -- By applying the hypothesis `h` to `z` and `x`, we get `z = op (op y z) (op y (op x y))`.
  have hz : ∀ y z, z = (‹Magma G›.op (‹Magma G›.op y z) (‹Magma G›.op y (‹Magma G›.op x y))) := by
    exact fun y z => h z y x;
  grind +ring

/-
Problem normal_0851: eq2495 → eq3854
-/
