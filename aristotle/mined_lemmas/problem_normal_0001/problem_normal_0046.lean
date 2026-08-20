

class Magma (G : Type _) where op : G → G → G
infixl:65 " ◇ " => Magma.op

/-
Problem normal_0001: eq2918 → eq1911
-/

theorem problem_normal_0046 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G), x = (y ◇ (x ◇ z)) ◇ (y ◇ x))
    : ∀ (x : G) (y : G) (z : G), x = (y ◇ y) ◇ ((y ◇ z) ◇ x) := by
  intros x y z; exact (by
  convert h x y z using 1;
  grind +qlia)

/-
Problem normal_0049: eq697 → eq2873
-/
