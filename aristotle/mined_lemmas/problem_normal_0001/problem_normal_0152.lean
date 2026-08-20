

class Magma (G : Type _) where op : G → G → G
infixl:65 " ◇ " => Magma.op

/-
Problem normal_0001: eq2918 → eq1911
-/

theorem problem_normal_0152 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G) (w : G), x = y ◇ (x ◇ ((y ◇ z) ◇ w)))
    : ∀ (x : G) (y : G) (z : G) (w : G), x = (y ◇ z) ◇ ((w ◇ x) ◇ w) := by
  intros x y z w
  have := h x y z w;
  convert h x _ _ _;
  rotate_left;
  convert h _ _ _ _;
  · exact x;
  · exact x;
  · exact x;
  · grind

/-
Problem normal_0153: eq2585 → eq223
-/
