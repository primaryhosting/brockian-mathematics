

class Magma (G : Type _) where op : G → G → G
infixl:65 " ◇ " => Magma.op

/-
Problem normal_0001: eq2918 → eq1911
-/

theorem problem_normal_0076 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x = ((y ◇ z) ◇ (x ◇ w)) ◇ u)
    : ∀ (x : G) (y : G), x = y ◇ (x ◇ x) := by
  intro x;
  have := h x x x x x;
  grind

/-
Problem normal_0077: eq3767 → eq4245
-/
