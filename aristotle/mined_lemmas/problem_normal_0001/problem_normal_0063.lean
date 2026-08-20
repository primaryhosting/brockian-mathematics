

class Magma (G : Type _) where op : G → G → G
infixl:65 " ◇ " => Magma.op

/-
Problem normal_0001: eq2918 → eq1911
-/

theorem problem_normal_0063 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G), x = ((y ◇ (x ◇ y)) ◇ y) ◇ z)
    : ∀ (x : G) (y : G) (z : G), x = ((y ◇ z) ◇ x) ◇ (z ◇ z) := by
  have h_mul : ∀ x y, x = ‹Magma G›.op ( ‹Magma G›.op ( ‹Magma G›.op y ( ‹Magma G›.op x y ) ) y ) x := by
    exact fun x y => h x y x;
  grind +revert

/-
Problem normal_0065: eq2213 → eq3360
-/
