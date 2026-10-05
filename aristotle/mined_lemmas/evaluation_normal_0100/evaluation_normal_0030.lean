import Mathlib

class Magma (G : Type _) where op : G → G → G
infixl:65 " ◇ " => Magma.op

/- evaluation_normal_0100: eq2136 → eq4498 -/

theorem evaluation_normal_0030 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G), x = ((x ◇ y) ◇ y) ◇ (y ◇ y))
    : ∀ (x : G) (y : G), x = ((x ◇ (y ◇ y)) ◇ y) ◇ y := by
  intro x y
  have e0 := h x (y ◇ y)
  have e1 := h (x ◇ (y ◇ y)) y
  have e2 := h (((x ◇ (y ◇ y)) ◇ y) ◇ y) (y ◇ y)
  grind

/- evaluation_normal_0024: eq1462 → eq4136 -/
