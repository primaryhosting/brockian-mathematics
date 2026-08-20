

class Magma (G : Type _) where op : G → G → G
infixl:65 " ◇ " => Magma.op

/-
Problem normal_0001: eq2918 → eq1911
-/

theorem problem_normal_0060 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G), x = y ◇ (((z ◇ y) ◇ x) ◇ y))
    : ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = y ◇ (z ◇ w) := by
  intro z w_0050;
  intro z_1 w0;
  convert h _ _ _ using 1;
  convert h _ _ _ using 1;
  congr! 1;
  grind;
  · exact z_1;
  · exact z_1;
  · exact z_1

/-
Problem normal_0062: eq2713 → eq2803
-/
