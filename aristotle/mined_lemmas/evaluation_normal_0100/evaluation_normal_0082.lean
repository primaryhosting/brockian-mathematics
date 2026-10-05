import Mathlib

class Magma (G : Type _) where op : G → G → G
infixl:65 " ◇ " => Magma.op

/- evaluation_normal_0100: eq2136 → eq4498 -/

theorem evaluation_normal_0082 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G), x = x ◇ ((y ◇ z) ◇ (y ◇ y)))
    : ∀ (x : G) (y : G) (z : G), x ◇ x = (x ◇ y) ◇ (z ◇ x) := by
  intro x y z
  have e0 := h y y y
  have e1 := h y y (x ◇ x)
  have e2 := h y (x ◇ x) x
  have e3 := h z y y
  have e4 := h z (x ◇ y) (x ◇ y)
  have e5 := h z (z ◇ x) (z ◇ x)
  have e6 := h (x ◇ x) x y
  have e7 := h (x ◇ x) x (x ◇ y)
  have e8 := h x x ((z ◇ y) ◇ (z ◇ z))
  have e9 := h x y (y ◇ y)
  have e10 := h x z ((y ◇ y) ◇ (y ◇ y))
  have e11 := h x (x ◇ x) (x ◇ (x ◇ x))
  have e12 := h (y ◇ y) y y
  have e13 := h (y ◇ y) y z
  have e14 := h (y ◇ y) (y ◇ y) ((y ◇ z) ◇ (y ◇ y))
  have e15 := h (z ◇ z) ((z ◇ x) ◇ y) ((x ◇ y) ◇ y)
  have e16 := h (z ◇ z) ((z ◇ x) ◇ y) ((z ◇ x) ◇ y)
  have e17 := h (z ◇ z) ((z ◇ x) ◇ z) ((z ◇ y) ◇ (z ◇ z))
  grind

/- evaluation_normal_0012: eq532 → eq608 -/
