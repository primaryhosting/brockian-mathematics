import Mathlib

class Magma (G : Type _) where op : G → G → G
infixl:65 " ◇ " => Magma.op

/- evaluation_normal_0100: eq2136 → eq4498 -/

theorem evaluation_normal_0024 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G), x = (x ◇ y) ◇ (z ◇ (x ◇ y)))
    : ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = ((x ◇ y) ◇ z) ◇ w := by
  intro x y z w
  have e0 := h x x w
  have e1 := h x y y
  have e2 := h y (x ◇ y) (x ◇ y)
  have e3 := h z x x
  have e4 := h w (x ◇ y) (x ◇ y)
  have e5 := h x w (z ◇ x)
  have e6 := h (x ◇ x) (w ◇ (x ◇ x)) (y ◇ (x ◇ y))
  have e7 := h (x ◇ x) (w ◇ (x ◇ x)) (w ◇ (x ◇ y))
  have e8 := h (x ◇ x) (y ◇ (x ◇ y)) z
  grind

/- evaluation_normal_0018: eq1065 → eq3 -/
