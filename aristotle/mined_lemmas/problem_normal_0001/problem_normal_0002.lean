

class Magma (G : Type _) where op : G → G → G
infixl:65 " ◇ " => Magma.op

/-
Problem normal_0001: eq2918 → eq1911
-/

theorem problem_normal_0002 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x ◇ y = z ◇ (w ◇ (u ◇ u)))
    : ∀ (x : G) (y : G) (z : G) (w : G), x ◇ (y ◇ y) = (z ◇ w) ◇ z := by
  intro x y z;
  convert h _ _ _ _ _ using 1;
  grind +splitImp;
  · exact x;
  · exact x;
  · exact x;
  · exact x;
  · exact x

/-
Problem normal_0005: eq905 → eq3050
-/
