

class Magma (G : Type _) where op : G → G → G
infixl:65 " ◇ " => Magma.op

/-
Problem normal_0001: eq2918 → eq1911
-/

theorem problem_normal_0125 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x ◇ y = z ◇ (w ◇ (z ◇ u)))
    : ∀ (x : G) (y : G) (z : G) (w : G), x ◇ x = (y ◇ (z ◇ w)) ◇ y := by
  grind

/-
Problem normal_0126: eq3110 → eq4441
-/
