import Mathlib.Tactic

class Magma (G : Type _) where op : G → G → G
set_option quotPrecheck false in
infixl:65 " ◇ " => Magma.op


-- Problem normal_0166: eq1359 → eq210

theorem problem_normal_0331 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G) (w : G), x = (y ◇ ((x ◇ z) ◇ z)) ◇ w)
    : ∀ (x : G) (y : G) (z : G) (w : G), x = (y ◇ (z ◇ y)) ◇ (w ◇ y) := by
  intro x y z w;
  have := h x y y;
  convert this ( _ ) using 1;
  swap;
  bv_omega;
  convert h _ _ _ _ using 1;
  congr! 1;
  congr! 1;
  convert h _ _ _ _ using 1;
  exact x

-- Problem normal_0336: eq2825 → eq3995
