

class Magma (G : Type _) where op : G → G → G
infixl:65 " ◇ " => Magma.op

/-
Problem normal_0001: eq2918 → eq1911
-/

theorem problem_normal_0110 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G) (w : G), x = ((y ◇ (x ◇ z)) ◇ y) ◇ w)
    : ∀ (x : G) (y : G) (z : G), x = y ◇ (((y ◇ x) ◇ y) ◇ z) := by
  -- Apply the given hypothesis h to rewrite the goal.
  intro x y z
  have := h x y z y;
  convert h _ _ _ _;
  convert h _ _ _ _;
  · exact x;
  · exact x

/-
Problem normal_0115: eq1362 → eq3324
-/
