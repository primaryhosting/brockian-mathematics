

class Magma (G : Type _) where op : G → G → G
infixl:65 " ◇ " => Magma.op

/-
Problem normal_0001: eq2918 → eq1911
-/

theorem problem_normal_0134 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G), x = y ◇ ((x ◇ x) ◇ z))
    : ∀ (x : G) (y : G) (z : G), x = (y ◇ (y ◇ y)) ◇ (z ◇ y) := by
  intro x y z;
  convert h x _ _ using 1;
  congr! 1;
  convert h _ _ _ using 1;
  exact x

/-
Problem normal_0137: eq3027 → eq55
-/
