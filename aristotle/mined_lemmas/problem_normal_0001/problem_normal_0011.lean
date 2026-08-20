

class Magma (G : Type _) where op : G → G → G
infixl:65 " ◇ " => Magma.op

/-
Problem normal_0001: eq2918 → eq1911
-/

theorem problem_normal_0011 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G), x = y ◇ (y ◇ ((z ◇ x) ◇ y)))
    : ∀ (x : G) (y : G) (z : G), x = ((y ◇ y) ◇ x) ◇ (z ◇ x) := by
  grind

/-
Problem normal_0018: eq1077 → eq747
-/
