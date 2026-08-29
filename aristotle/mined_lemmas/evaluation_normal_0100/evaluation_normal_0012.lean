import Mathlib

class Magma (G : Type _) where op : G → G → G
infixl:65 " ◇ " => Magma.op

/- evaluation_normal_0100: eq2136 → eq4498 -/

theorem evaluation_normal_0012 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G) (w : G), x = y ◇ (y ◇ (z ◇ (w ◇ x))))
    : ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x = y ◇ (z ◇ (w ◇ (u ◇ x))) := by
  intro x y z w u
  have e0 := h x z w u
  have e1 := h x (y ◇ (z ◇ (w ◇ (u ◇ x)))) (y ◇ (z ◇ (w ◇ (u ◇ x)))) (z ◇ (w ◇ (u ◇ x)))
  have e2 := h (z ◇ (w ◇ (u ◇ x))) (y ◇ (z ◇ (w ◇ (u ◇ x)))) (z ◇ (w ◇ (u ◇ x))) y
  have e3 := h (z ◇ (w ◇ (u ◇ x))) (y ◇ (z ◇ (w ◇ (u ◇ x)))) (z ◇ (w ◇ (u ◇ x))) z
  have e4 := h (y ◇ (z ◇ (w ◇ (u ◇ x)))) (y ◇ (z ◇ (w ◇ (u ◇ x)))) (y ◇ (z ◇ (w ◇ (u ◇ x))))
    (z ◇ (w ◇ (u ◇ x)))
  grind

/- evaluation_normal_0084: eq868 → eq438 -/
