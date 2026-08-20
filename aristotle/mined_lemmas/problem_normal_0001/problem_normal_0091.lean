

class Magma (G : Type _) where op : G → G → G
infixl:65 " ◇ " => Magma.op

/-
Problem normal_0001: eq2918 → eq1911
-/

theorem problem_normal_0091 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G) (w : G), x = (y ◇ ((y ◇ x) ◇ z)) ◇ w)
    : ∀ (x : G) (y : G) (z : G), x ◇ y = z ◇ ((y ◇ x) ◇ x) := by
  intro x y z;
  convert h _ _ _ _;
  convert h z y x _ using 1;
  exact x

/-
Problem normal_0092: eq2581 → eq444
-/
