import Mathlib

class Magma (G : Type _) where op : G → G → G
infixl:65 " ◇ " => Magma.op

/- evaluation_normal_0100: eq2136 → eq4498 -/

theorem evaluation_normal_0160 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x = (x ◇ (y ◇ z)) ◇ (w ◇ u))
    : ∀ (x : G) (y : G) (z : G), x = (x ◇ (x ◇ (y ◇ z))) ◇ y := by
  intro x y z
  have e0 := h x y z (x ◇ (x ◇ (y ◇ z))) y
  have e1 := h y (x ◇ (y ◇ z)) ((x ◇ (x ◇ (y ◇ z))) ◇ y) (x ◇ (y ◇ z))
    ((x ◇ (x ◇ (y ◇ z))) ◇ y)
  have e2 := h x x (y ◇ z) (y ◇ x) x
  grind

/- evaluation_normal_0030: eq2064 → eq2876 -/
