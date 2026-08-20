

class Magma (G : Type _) where op : G → G → G
infixl:65 " ◇ " => Magma.op

/-
Problem normal_0001: eq2918 → eq1911
-/

theorem problem_normal_0137 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G) (w : G), x = ((y ◇ (z ◇ w)) ◇ x) ◇ w)
    : ∀ (x : G) (y : G), x = x ◇ (y ◇ (y ◇ x)) := by
  intro x y;
  convert h x _ _ _;
  convert h x _ _ _ using 1;
  convert rfl;
  convert h x _ _ _;
  · exact x;
  · exact x;
  · exact x;
  · exact x

/-
Problem normal_0138: eq116 → eq4576
-/
