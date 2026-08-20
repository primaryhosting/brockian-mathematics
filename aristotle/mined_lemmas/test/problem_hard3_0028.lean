

theorem problem_hard3_0028 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G), x = y ◇ ((z ◇ x) ◇ x))
    : ∀ (x : G) (y : G) (z : G) (w : G), x = ((y ◇ z) ◇ w) ◇ (z ◇ x) := by
  intro x y z w; have := h x x x; grind

