

class Magma (G : Type _) where op : G → G → G
infixl:65 " ◇ " => Magma.op

/-
Problem normal_0001: eq2918 → eq1911
-/

theorem problem_normal_0132 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G), x = y ◇ ((z ◇ (x ◇ z)) ◇ z))
    : ∀ (x : G) (y : G) (z : G), x = (y ◇ (y ◇ z)) ◇ (y ◇ z) := by
  intro x y z;
  convert h x _ _ using 1;
  rotate_left;
  exact y;
  exact y;
  convert h _ _ _ using 1;
  congr! 1;
  convert h _ _ _ using 1;
  exact x

/-
Problem normal_0134: eq116 → eq1938
-/
