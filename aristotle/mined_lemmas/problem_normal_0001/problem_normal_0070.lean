

class Magma (G : Type _) where op : G → G → G
infixl:65 " ◇ " => Magma.op

/-
Problem normal_0001: eq2918 → eq1911
-/

theorem problem_normal_0070 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G), x ◇ y = (y ◇ y) ◇ z)
    : ∀ (x : G) (y : G) (z : G), x ◇ (y ◇ z) = (x ◇ x) ◇ y := by
  grind

/-
Problem normal_0072: eq3002 → eq2281
-/
