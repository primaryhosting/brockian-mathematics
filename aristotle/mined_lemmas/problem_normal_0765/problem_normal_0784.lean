
import Mathlib.Tactic

set_option quotPrecheck false
class Magma (G : Type _) where op : G → G → G
infixl:65 " ◇ " => Magma.op

/-
Problem normal_0765: eq1708 → eq3230
-/

theorem problem_normal_0784 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G) (w : G), x = (((y ◇ x) ◇ z) ◇ y) ◇ w)
    : ∀ (x : G) (y : G) (z : G), x ◇ x = ((y ◇ x) ◇ x) ◇ z := by
  intro x y;
  convert h ( _ ) y x x using 1;
  constructor;
  grind;
  intro h z;
  rename_i h';
  convert h' _ _ _ _ using 1;
  congr! 1;
  convert h' _ _ _ _ using 1;
  exact x;
  exact x

/-
Problem normal_0793: eq1118 → eq3486
-/
