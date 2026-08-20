

class Magma (G : Type _) where op : G → G → G
infixl:65 " ◇ " => Magma.op

/-
Problem normal_0001: eq2918 → eq1911
-/

theorem problem_normal_0083 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G), x = (y ◇ ((x ◇ z) ◇ x)) ◇ y)
    : ∀ (x : G) (y : G) (z : G) (w : G), x = (y ◇ z) ◇ ((x ◇ y) ◇ w) := by
  intro x y z
  have := h x y z;
  rename_i h';
  intro w
  have := h (h'.op (h'.op y z) (h'.op (h'.op x y) w)) y z
  simp at this;
  grind +revert

/-
Problem normal_0087: eq886 → eq4057
-/
