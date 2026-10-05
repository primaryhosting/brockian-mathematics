import Mathlib

class Magma (G : Type _) where op : G → G → G
infixl:65 " ◇ " => Magma.op

/- evaluation_normal_0100: eq2136 → eq4498 -/

theorem evaluation_normal_0100 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G), x = ((y ◇ y) ◇ y) ◇ (x ◇ z))
    : ∀ (x : G) (y : G) (z : G), x ◇ (y ◇ y) = (z ◇ z) ◇ y := by
  intro x y z
  have e0 := h x (y ◇ (y ◇ y)) x
  have e1 := h (x ◇ x) z x
  have e2 := h (y ◇ y) (y ◇ (y ◇ y)) y
  have e3 := h (z ◇ z) (y ◇ (y ◇ y)) z
  have e4 := h ((y ◇ y) ◇ y) (y ◇ (y ◇ y)) ((z ◇ z) ◇ z)
  have e5 := h ((z ◇ z) ◇ z) y ((z ◇ z) ◇ z)
  have e6 := h ((z ◇ z) ◇ z) z (x ◇ (z ◇ z))
  have e7 := h ((z ◇ z) ◇ z) z ((z ◇ z) ◇ z)
  have e8 := h ((z ◇ z) ◇ z) (y ◇ (y ◇ y)) (x ◇ x)
  have e9 := h ((z ◇ z) ◇ z) (y ◇ (y ◇ y)) ((x ◇ x) ◇ x)
  grind

/- evaluation_normal_0082: eq857 → eq3670 -/
