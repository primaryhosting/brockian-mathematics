

class Magma (G : Type _) where op : G → G → G
infixl:65 " ◇ " => Magma.op

/-
Problem normal_0001: eq2918 → eq1911
-/

theorem problem_normal_0032 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G), x ◇ y = y ◇ (z ◇ (y ◇ z)))
    : ∀ (x : G) (y : G) (z : G), x ◇ y = y ◇ ((y ◇ z) ◇ z) := by
  grind

/-
Problem normal_0035: eq1775 → eq1961
-/
