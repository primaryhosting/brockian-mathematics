

class Magma (G : Type _) where op : G → G → G
infixl:65 " ◇ " => Magma.op

/-
Problem normal_0001: eq2918 → eq1911
-/

theorem problem_normal_0077 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = (y ◇ y) ◇ (z ◇ w))
    : ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = ((z ◇ w) ◇ x) ◇ w := by
  grind

/-
Problem normal_0079: eq1290 → eq4513
-/
