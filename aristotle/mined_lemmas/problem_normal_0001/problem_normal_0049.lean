

class Magma (G : Type _) where op : G → G → G
infixl:65 " ◇ " => Magma.op

/-
Problem normal_0001: eq2918 → eq1911
-/

theorem problem_normal_0049 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G) (w : G), x = y ◇ (x ◇ ((z ◇ z) ◇ w)))
    : ∀ (x : G) (y : G), x = ((x ◇ (y ◇ y)) ◇ x) ◇ y := by
  intros x y;
  convert h x _ _ _;
  convert h y x _ _ using 1;
  congr! 1;
  convert h _ _ _ _;
  · exact x;
  · exact x;
  · exact x

/-
Problem normal_0050: eq1495 → eq2220
-/
