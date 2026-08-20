

class Magma (G : Type _) where op : G → G → G
infixl:65 " ◇ " => Magma.op

/-
Problem normal_0001: eq2918 → eq1911
-/

theorem problem_normal_0072 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G) (w : G), x = ((y ◇ (z ◇ y)) ◇ w) ◇ x)
    : ∀ (x : G) (y : G) (z : G), x = (x ◇ (y ◇ (z ◇ z))) ◇ x := by
  intro x y z;
  convert h x x y ( _ ) using 1;
  convert h _ _ _ _;
  · convert h x x z ( _ );
    convert h x z z ( _ ) using 1;
    swap;
    grind;
    convert h _ _ _ _ using 1;
    convert h _ _ _ _;
    · grind;
    · convert h _ _ _ _;
      rotate_left;
      bv_omega;
      exact z;
      grind;
      grind;
    · exact x;
    · exact x;
    · exact x;
  · exact x

/-
Problem normal_0076: eq2786 → eq13
-/
