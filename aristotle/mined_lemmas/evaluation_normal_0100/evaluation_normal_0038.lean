import Mathlib

class Magma (G : Type _) where op : G → G → G
infixl:65 " ◇ " => Magma.op

/- evaluation_normal_0100: eq2136 → eq4498 -/

theorem evaluation_normal_0038 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G), x = ((y ◇ (y ◇ x)) ◇ x) ◇ x)
    : ∀ (x : G), x = (x ◇ x) ◇ x := by
  intro x
  have e0 := h x x
  have e1 := h x ((x ◇ (x ◇ x)) ◇ x)
  grind

