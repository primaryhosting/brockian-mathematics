import Mathlib

class Magma (G : Type _) where op : G → G → G
infixl:65 " ◇ " => Magma.op

/- evaluation_normal_0100: eq2136 → eq4498 -/

theorem evaluation_normal_0104 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G), x = (x ◇ (x ◇ (y ◇ x))) ◇ z)
    : ∀ (x : G) (y : G), x ◇ x = ((x ◇ x) ◇ y) ◇ y := by
  intro x y
  have e0 := h x y x
  have e1 := h x y (x ◇ (x ◇ x))
  have e2 := h x (x ◇ (x ◇ (y ◇ x))) x
  have e3 := h x (x ◇ (x ◇ (y ◇ x))) y
  have e4 := h (x ◇ (x ◇ x)) (x ◇ (x ◇ (y ◇ x))) x
  have e5 := h (x ◇ (x ◇ x)) (x ◇ (x ◇ (y ◇ x))) y
  grind

/- evaluation_normal_0160: eq1883 → eq2250 -/
