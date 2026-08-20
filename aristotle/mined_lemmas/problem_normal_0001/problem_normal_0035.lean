

class Magma (G : Type _) where op : G → G → G
infixl:65 " ◇ " => Magma.op

/-
Problem normal_0001: eq2918 → eq1911
-/

theorem problem_normal_0035 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G) (w : G), x = (y ◇ z) ◇ ((y ◇ x) ◇ w))
    : ∀ (x : G) (y : G) (z : G) (w : G), x = (y ◇ (z ◇ x)) ◇ (x ◇ w) := by
  intro x y z w;
  -- Apply the hypothesis `h` to the expression `x = y ◇ z ◇ (y ◇ x ◇ w)`.
  have := h x y z w;
  have := h ( ‹Magma G›.op y z ) y z w;
  have := h ( ‹Magma G›.op y ( ‹Magma G›.op y z ) ) y z w;
  grind

/-
Problem normal_0042: eq1971 → eq3301
-/
