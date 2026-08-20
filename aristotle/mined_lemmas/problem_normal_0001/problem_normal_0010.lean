

class Magma (G : Type _) where op : G → G → G
infixl:65 " ◇ " => Magma.op

/-
Problem normal_0001: eq2918 → eq1911
-/

theorem problem_normal_0010 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = (z ◇ w) ◇ (w ◇ z))
    : ∀ (x : G) (y : G), (x ◇ x) ◇ y = (y ◇ x) ◇ x := by
  grind

/-
Problem normal_0011: eq724 → eq2130
-/
