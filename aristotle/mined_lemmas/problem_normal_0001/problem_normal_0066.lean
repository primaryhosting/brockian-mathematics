

class Magma (G : Type _) where op : G → G → G
infixl:65 " ◇ " => Magma.op

/-
Problem normal_0001: eq2918 → eq1911
-/

theorem problem_normal_0066 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = (z ◇ z) ◇ (w ◇ x))
    : ∀ (x : G) (y : G) (z : G), x ◇ x = (x ◇ (y ◇ x)) ◇ z := by
  intros x y z;
  convert h x x z x using 1;
  grind

/-
Problem normal_0068: eq3846 → eq3413
-/
