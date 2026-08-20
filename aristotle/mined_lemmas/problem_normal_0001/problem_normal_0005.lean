

class Magma (G : Type _) where op : G → G → G
infixl:65 " ◇ " => Magma.op

/-
Problem normal_0001: eq2918 → eq1911
-/

theorem problem_normal_0005 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x = y ◇ ((x ◇ z) ◇ (w ◇ u)))
    : ∀ (x : G), x = (((x ◇ x) ◇ x) ◇ x) ◇ x := by
  intro x;
  convert h x _ _ _ _ using 1;
  convert h _ _ _ _ _;
  · convert h x _ _ _ _ using 1;
    rotate_left;
    exact ‹Magma G›.op ( ‹Magma G›.op ( ‹Magma G›.op x x ) x ) x;
    exact x;
    exact x;
    exact x;
    grind;
  · exact x;
  · exact x;
  · exact x;
  · exact x

/-
Problem normal_0010: eq3853 → eq4605
-/
