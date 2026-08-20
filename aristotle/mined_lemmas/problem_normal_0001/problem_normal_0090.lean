

class Magma (G : Type _) where op : G → G → G
infixl:65 " ◇ " => Magma.op

/-
Problem normal_0001: eq2918 → eq1911
-/

theorem problem_normal_0090 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G), x = (y ◇ (z ◇ (z ◇ x))) ◇ x)
    : ∀ (x : G) (y : G), x = (x ◇ ((y ◇ x) ◇ x)) ◇ x := by
  have := h;
  convert this using 3;
  grind +splitImp

/-
Problem normal_0091: eq2539 → eq3599
-/
