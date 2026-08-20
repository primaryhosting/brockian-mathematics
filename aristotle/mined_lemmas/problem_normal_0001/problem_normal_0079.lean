

class Magma (G : Type _) where op : G → G → G
infixl:65 " ◇ " => Magma.op

/-
Problem normal_0001: eq2918 → eq1911
-/

theorem problem_normal_0079 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G), x = y ◇ (((x ◇ y) ◇ y) ◇ z))
    : ∀ (x : G) (y : G) (z : G) (w : G), x ◇ (y ◇ z) = (x ◇ y) ◇ w := by
  -- Let's assume the given identity and derive the required equality.
  intros x y z w
  have := h x y z;
  convert h _ _ _ using 1;
  convert h _ _ _ using 1;
  convert h _ _ _ using 1;
  convert rfl;
  convert h _ _ _ using 1;
  convert h _ _ _ using 1;
  congr! 1;
  convert h _ _ _ using 1;
  exact y;
  · exact x;
  · exact x;
  · exact x;
  · exact x;
  · exact x

/-
Problem normal_0083: eq2514 → eq1762
-/
