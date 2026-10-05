import Mathlib

class Magma (G : Type _) where op : G → G → G
infixl:65 " ◇ " => Magma.op

/- evaluation_normal_0100: eq2136 → eq4498 -/

theorem evaluation_normal_0084 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x = x ◇ ((y ◇ z) ◇ (w ◇ u)))
    : ∀ (x : G) (y : G) (z : G), x = x ◇ (y ◇ (y ◇ (x ◇ z))) := by
  intro x y z
  have e0 := h x (y ◇ (y ◇ (x ◇ z))) (y ◇ (y ◇ (x ◇ z))) (y ◇ (y ◇ (x ◇ z))) (y ◇ (y ◇ (x ◇ z)))
  have e1 := h (y ◇ (y ◇ (x ◇ z))) y (y ◇ (x ◇ z)) y (y ◇ (x ◇ z))
  have e2 := h (y ◇ (y ◇ (x ◇ z))) y (y ◇ (x ◇ z)) (y ◇ (y ◇ (x ◇ z))) (y ◇ (y ◇ (x ◇ z)))
  grind

/- evaluation_normal_0112: eq2546 → eq4209 -/
