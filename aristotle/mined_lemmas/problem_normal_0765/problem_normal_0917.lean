
import Mathlib.Tactic

set_option quotPrecheck false
class Magma (G : Type _) where op : G → G → G
infixl:65 " ◇ " => Magma.op

/-
Problem normal_0765: eq1708 → eq3230
-/

theorem problem_normal_0917 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G), x = y ◇ ((z ◇ (y ◇ x)) ◇ y))
    : ∀ (x : G) (y : G) (z : G), (x ◇ y) ◇ y = (y ◇ z) ◇ x := by
  revert ‹_›;
  rename_i G';
  intro h!;
  have h1 : ∀ x y : G, x = G'.op y (G'.op (G'.op y (G'.op y x)) y) := by
    exact fun x y => h! x y y;
  grind

/-
Problem normal_0919: eq1294 → eq4664
-/
