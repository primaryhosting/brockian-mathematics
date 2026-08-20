
import Mathlib.Tactic

set_option quotPrecheck false
class Magma (G : Type _) where op : G → G → G
infixl:65 " ◇ " => Magma.op

/-
Problem normal_0765: eq1708 → eq3230
-/

theorem problem_normal_0938 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G) (w : G), x = y ◇ (((z ◇ x) ◇ y) ◇ w))
    : ∀ (x : G) (y : G), x = y ◇ (y ◇ (y ◇ y)) := by
  intro x y;
  convert h x y x x using 1;
  convert h y y y y using 1;
  · convert h y y y y |> Eq.symm using 1;
    grind;
  · grind

/-
Problem normal_0940: eq553 → eq3702
-/
