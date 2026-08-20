

class Magma (G : Type _) where op : G → G → G
infixl:65 " ◇ " => Magma.op

/-
Problem normal_0001: eq2918 → eq1911
-/

theorem problem_normal_0153 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G), x = (y ◇ ((z ◇ y) ◇ x)) ◇ y)
    : ∀ (x : G) (y : G) (z : G), x = (y ◇ (x ◇ y)) ◇ z := by
  intro x y z;
  convert h x y z using 1;
  grind

/-
Problem normal_0154: eq2957 → eq200
-/
