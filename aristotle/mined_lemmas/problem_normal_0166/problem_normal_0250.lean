import Mathlib.Tactic

class Magma (G : Type _) where op : G → G → G
set_option quotPrecheck false in
infixl:65 " ◇ " => Magma.op


-- Problem normal_0166: eq1359 → eq210

theorem problem_normal_0250 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x = (y ◇ ((x ◇ z) ◇ w)) ◇ u)
    : ∀ (x : G) (y : G) (z : G), x = y ◇ (((x ◇ y) ◇ z) ◇ y) := by
  intro x y z;
  convert h x y ( ‹Magma G›.op x y ) z y using 3;
  · convert h y y x x y using 1;
    grind;
  · convert h y _ _ _ _ using 1;
    rotate_left;
    convert h y x y z y using 1;
    convert h _ _ _ _ _ |> Eq.symm using 1;
    rotate_left;
    exact (x ◇ x);
    exact (x ◇ x);
    exact y;
    exact y;
    grind

/-
Problem normal_0253: eq2780 → eq4363
-/
