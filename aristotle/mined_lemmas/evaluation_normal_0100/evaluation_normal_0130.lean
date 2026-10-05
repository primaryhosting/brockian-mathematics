import Mathlib

class Magma (G : Type _) where op : G → G → G
infixl:65 " ◇ " => Magma.op

/- evaluation_normal_0100: eq2136 → eq4498 -/

theorem evaluation_normal_0130 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G), x = x ◇ ((y ◇ y) ◇ (x ◇ z)))
    : ∀ (x : G) (y : G), x ◇ y = (x ◇ y) ◇ (y ◇ y) := by
  intro x y
  have e0 := h (x ◇ y) ((y ◇ y) ◇ (y ◇ y)) (x ◇ y)
  have e1 := h (y ◇ y) y (x ◇ (x ◇ y))
  have e2 := h (y ◇ y) y ((y ◇ y) ◇ (x ◇ (x ◇ y)))
  have e3 := h (y ◇ y) (x ◇ y) ((x ◇ y) ◇ y)
  have e4 := h (y ◇ y) (x ◇ y) ((y ◇ y) ◇ (y ◇ y))
  have e5 := h ((x ◇ y) ◇ (x ◇ y)) (y ◇ y) ((y ◇ y) ◇ ((x ◇ y) ◇ y))
  grind

/- evaluation_normal_0168: eq2020 → eq1743 -/
