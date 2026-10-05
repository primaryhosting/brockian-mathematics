import Mathlib

class Magma (G : Type _) where op : G → G → G
infixl:65 " ◇ " => Magma.op

/- evaluation_normal_0100: eq2136 → eq4498 -/

theorem evaluation_normal_0112 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G), x = (y ◇ ((y ◇ y) ◇ z)) ◇ x)
    : ∀ (x : G) (y : G) (z : G), x ◇ y = ((z ◇ y) ◇ x) ◇ y := by
  intro x y z
  have e0 := h (z ◇ y) ((z ◇ y) ◇ x) x
  have e1 := h ((z ◇ y) ◇ x) x x
  have e2 := h ((z ◇ y) ◇ x) x ((z ◇ y) ◇ x)
  have e3 := h x ((z ◇ z) ◇ z) x
  have e4 := h x ((z ◇ z) ◇ z) ((z ◇ z) ◇ z)
  have e5 := h ((z ◇ z) ◇ z) (x ◇ ((x ◇ x) ◇ x)) ((z ◇ z) ◇ z)
  have e6 := h ((z ◇ z) ◇ z) (x ◇ ((x ◇ x) ◇ x)) (x ◇ ((x ◇ x) ◇ x))
  have e7 := h (x ◇ ((x ◇ x) ◇ x)) x x
  have e8 := h (x ◇ ((x ◇ x) ◇ x)) x (z ◇ y)
  have e9 := h (x ◇ ((x ◇ x) ◇ x)) x ((z ◇ y) ◇ x)
  grind

/- evaluation_normal_0044: eq3366 → eq3390 -/
