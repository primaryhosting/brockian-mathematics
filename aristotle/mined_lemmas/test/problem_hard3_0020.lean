

theorem problem_hard3_0020 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G), x = y ◇ (z ◇ (z ◇ x)))
    : ∀ (x : G) (y : G), x = (x ◇ x) ◇ (x ◇ (y ◇ x)) := by
  intro x y; have := h x x x; grind

