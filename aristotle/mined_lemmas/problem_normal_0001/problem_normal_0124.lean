

class Magma (G : Type _) where op : G → G → G
infixl:65 " ◇ " => Magma.op

/-
Problem normal_0001: eq2918 → eq1911
-/

theorem problem_normal_0124 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G), x = (y ◇ y) ◇ ((x ◇ z) ◇ y))
    : ∀ (x : G) (y : G) (z : G) (w : G), x = (y ◇ ((z ◇ w) ◇ w)) ◇ z := by
  intro x y z w
  have := h x y z
  have := h y z w
  have := h z w y
  have := h w y z;
  grind +ring

/-
Problem normal_0125: eq3444 → eq3910
-/
