

class Magma (G : Type _) where op : G → G → G
infixl:65 " ◇ " => Magma.op

/-
Problem normal_0001: eq2918 → eq1911
-/

theorem problem_normal_0069 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G) (w : G), x = ((y ◇ (z ◇ z)) ◇ x) ◇ w)
    : ∀ (x : G) (y : G) (z : G), (x ◇ y) ◇ z = (y ◇ x) ◇ z := by
  intro x y z;
  convert h _ _ _ _;
  rotate_left;
  convert h _ _ _ _ using 1;
  rotate_left;
  exact x;
  grind;
  grind;
  exact x;
  grind;
  · convert h _ _ _ _;
    convert h _ _ _ _;
    rotate_left;
    exact x;
    exact x;
    exact x;
    convert h _ _ _ _;
    rotate_left;
    grind;
    exact x;
    exact x;
    grind;
  · grind

/-
Problem normal_0070: eq389 → eq4507
-/
