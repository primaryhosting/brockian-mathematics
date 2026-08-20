

class Magma (G : Type _) where op : G → G → G
infixl:65 " ◇ " => Magma.op

/-
Problem normal_0001: eq2918 → eq1911
-/

theorem problem_normal_0101 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = ((z ◇ y) ◇ y) ◇ w)
    : ∀ (x : G) (y : G) (z : G), x ◇ y = (y ◇ x) ◇ z := by
  intro x y z;
  convert h x y y z using 1;
  grind

/-
Problem normal_0110: eq2926 → eq1317
-/
