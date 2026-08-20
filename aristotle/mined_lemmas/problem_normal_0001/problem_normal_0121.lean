

class Magma (G : Type _) where op : G → G → G
infixl:65 " ◇ " => Magma.op

/-
Problem normal_0001: eq2918 → eq1911
-/

theorem problem_normal_0121 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = y ◇ ((z ◇ w) ◇ w))
    : ∀ (x : G) (y : G) (z : G), x ◇ (x ◇ y) = z ◇ (y ◇ y) := by
  grind

/-
Problem normal_0122: eq74 → eq2583
-/
