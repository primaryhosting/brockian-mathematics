

class Magma (G : Type _) where op : G → G → G
infixl:65 " ◇ " => Magma.op

/-
Problem normal_0001: eq2918 → eq1911
-/

theorem problem_normal_0126 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G), x = (((y ◇ x) ◇ x) ◇ z) ◇ z)
    : ∀ (x : G) (y : G) (z : G) (w : G), x ◇ (y ◇ x) = (x ◇ z) ◇ w := by
  intros x y z w
  have := h x y z
  have := h y z w
  have := h z w x
  have := h w x y
  have := h x z w
  have := h y w x
  have := h z x y
  have := h w y z
  have := h x w y
  have := h y x z
  have := h z y w
  have := h w z x;
  grind

/-
Problem normal_0132: eq1156 → eq1947
-/
