

class Magma (G : Type _) where op : G → G → G
infixl:65 " ◇ " => Magma.op

/-
Problem normal_0001: eq2918 → eq1911
-/

theorem problem_normal_0022 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G), x = ((y ◇ y) ◇ (x ◇ y)) ◇ z)
    : ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x ◇ y = z ◇ (w ◇ (u ◇ y)) := by
  intro x y z u;
  have := h x y;
  have := h z;
  rename_i h;
  rw [ h, this ];
  grind;
  exact x

/-
Problem normal_0023: eq2311 → eq3542
-/
