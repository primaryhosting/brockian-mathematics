import Mathlib.Tactic

class Magma (G : Type _) where op : G → G → G
set_option quotPrecheck false in
infixl:65 " ◇ " => Magma.op


-- Problem normal_0166: eq1359 → eq210

theorem problem_normal_0287 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G), x = ((y ◇ z) ◇ (x ◇ y)) ◇ y)
    : ∀ (x : G) (y : G) (z : G), x ◇ y = (x ◇ (z ◇ z)) ◇ y := by
  intro x y z;
  convert h ( _ ) _ _ using 1;
  convert h _ _ _ using 1;
  convert rfl;
  · convert h _ _ _ using 1;
    convert h _ _ _ using 1;
    rotate_left;
    exact (x ◇ x);
    exact (x ◇ x);
    exact (x ◇ x);
    exact (x ◇ x);
    grind;
  · exact x;
  · exact x

/-
Problem normal_0289: eq1715 → eq374
-/
