

class Magma (G : Type _) where op : G → G → G
infixl:65 " ◇ " => Magma.op

/-
Problem normal_0001: eq2918 → eq1911
-/

theorem problem_normal_0001 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G) (w : G), x = ((y ◇ (x ◇ y)) ◇ z) ◇ w)
    : ∀ (x : G) (y : G) (z : G) (w : G), x = (y ◇ (x ◇ z)) ◇ (y ◇ w) := by
  intro x y z w;
  convert h _ _ _ _;
  convert h _ _ _ _;
  · exact x;
  · exact x

/-
Problem normal_0002: eq3454 → eq4503
-/
