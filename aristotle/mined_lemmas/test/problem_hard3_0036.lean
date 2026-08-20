

theorem problem_hard3_0036 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G), x = (x ◇ (x ◇ x)) ◇ y)
    : ∀ (x : G), x = (x ◇ x) ◇ (x ◇ (x ◇ x)) := by
  intro x
  have h1 := h x x; have h2 := h x (x ◇ (x ◇ x)); have h3 := h (x ◇ x) x; grind

