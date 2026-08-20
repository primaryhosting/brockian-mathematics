

class Magma (G : Type _) where op : G → G → G
infixl:65 " ◇ " => Magma.op

/-
Problem normal_0001: eq2918 → eq1911
-/

theorem problem_normal_0092 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G) (w : G), x = (y ◇ ((z ◇ x) ◇ w)) ◇ z)
    : ∀ (x : G) (y : G) (z : G), x = x ◇ (y ◇ (y ◇ (z ◇ z))) := by
  intros x y z;
  convert h x y y ( ⁅y, z⁆ ) using 1;
  swap;
  exact ⟨ fun _ _ => ‹Magma G›.op ‹_› ‹_› ⟩;
  convert h _ _ _ _;
  convert h x _ _ _;
  convert h x _ _ _;
  · exact x;
  · exact x;
  · exact x

/-
Problem normal_0099: eq878 → eq3784
-/
