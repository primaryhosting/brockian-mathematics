

class Magma (G : Type _) where op : G → G → G
infixl:65 " ◇ " => Magma.op

/-
Problem normal_0001: eq2918 → eq1911
-/

theorem problem_normal_0115 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G) (w : G), x = y ◇ (((z ◇ x) ◇ w) ◇ y))
    : ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = x ◇ (y ◇ (z ◇ w)) := by
  grind

/-
Problem normal_0121: eq3580 → eq4304
-/
