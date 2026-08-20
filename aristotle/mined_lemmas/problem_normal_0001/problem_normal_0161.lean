

class Magma (G : Type _) where op : G → G → G
infixl:65 " ◇ " => Magma.op

/-
Problem normal_0001: eq2918 → eq1911
-/

theorem problem_normal_0161 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G), x = y ◇ (y ◇ ((x ◇ z) ◇ z)))
    : ∀ (x : G) (y : G) (z : G), x ◇ y = y ◇ ((z ◇ x) ◇ z) := by
  intro x y z;
  have h1 := h x x z;
  have h3 := h y z x;
  have h4 := h z y x;
  grind
