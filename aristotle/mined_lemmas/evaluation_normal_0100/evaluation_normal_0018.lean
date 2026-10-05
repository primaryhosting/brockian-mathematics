import Mathlib

class Magma (G : Type _) where op : G → G → G
infixl:65 " ◇ " => Magma.op

/- evaluation_normal_0100: eq2136 → eq4498 -/

theorem evaluation_normal_0018 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G), x = x ◇ ((y ◇ (z ◇ z)) ◇ z))
    : ∀ (x : G), x = x ◇ x := by
  intro x
  have e0 := h x ((x ◇ x) ◇ (x ◇ x)) ((x ◇ x) ◇ (x ◇ x))
  have e1 := h (x ◇ x) (x ◇ x) ((x ◇ x) ◇ (x ◇ x))
  have e2 := h (x ◇ x) ((x ◇ x) ◇ (x ◇ x)) ((x ◇ x) ◇ (x ◇ x))
  have e3 := h (x ◇ (x ◇ x)) (x ◇ (x ◇ x)) ((x ◇ x) ◇ (x ◇ x))
  have e4 := h ((x ◇ (x ◇ x)) ◇ x) x x
  have e5 := h ((x ◇ x) ◇ (x ◇ x)) ((x ◇ (x ◇ x)) ◇ x) ((x ◇ (x ◇ x)) ◇ x)
  have e6 := h ((x ◇ x) ◇ (x ◇ x)) ((x ◇ x) ◇ (x ◇ x)) ((x ◇ (x ◇ x)) ◇ x)
  grind

/- evaluation_normal_0004: eq134 → eq1400 -/
