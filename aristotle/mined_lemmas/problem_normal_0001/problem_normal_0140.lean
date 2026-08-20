

class Magma (G : Type _) where op : G → G → G
infixl:65 " ◇ " => Magma.op

/-
Problem normal_0001: eq2918 → eq1911
-/

theorem problem_normal_0140 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G), x = (y ◇ (z ◇ (z ◇ x))) ◇ y)
    : ∀ (x : G), x = (x ◇ (x ◇ x)) ◇ (x ◇ x) := by
  intro x;
  convert h x _ _ using 1;
  rotate_left;
  exact x;
  exact x;
  grind

/-
Problem normal_0144: eq1900 → eq1966
-/
