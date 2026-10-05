import Mathlib

class Magma (G : Type _) where op : G → G → G
infixl:65 " ◇ " => Magma.op

/- evaluation_normal_0100: eq2136 → eq4498 -/

theorem evaluation_normal_0044 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G), x ◇ y = y ◇ (z ◇ (y ◇ x)))
    : ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = z ◇ (x ◇ (z ◇ w)) := by
  intro x y z w
  have e0 := h x y (x ◇ y)
  have e1 := h x (z ◇ (x ◇ (z ◇ w))) z
  have e2 := h y x (z ◇ (x ◇ (z ◇ w)))
  have e3 := h y (z ◇ (x ◇ (z ◇ w))) (z ◇ (x ◇ (z ◇ w)))
  have e4 := h z w x
  have e5 := h z w z
  have e6 := h z w (x ◇ (z ◇ w))
  have e7 := h z (z ◇ (x ◇ (z ◇ w))) z
  have e8 := h w z x
  have e9 := h w z z
  have e10 := h w z (x ◇ (z ◇ w))
  have e11 := h w z (z ◇ (x ◇ (z ◇ w)))
  have e12 := h (z ◇ (x ◇ (z ◇ w))) x z
  have e13 := h (z ◇ (x ◇ (z ◇ w))) x w
  have e14 := h (z ◇ (x ◇ (z ◇ w))) y (x ◇ y)
  have e15 := h (z ◇ (x ◇ (z ◇ w))) y (z ◇ (x ◇ (z ◇ w)))
  have e16 := h (z ◇ (x ◇ (z ◇ w))) z w
  have e17 := h (z ◇ (x ◇ (z ◇ w))) z (z ◇ (x ◇ (z ◇ w)))
  have e18 := h (z ◇ (x ◇ (z ◇ w))) (x ◇ y) x
  have e19 := h (z ◇ (x ◇ (z ◇ w))) (x ◇ y) y
  have e20 := h (z ◇ (x ◇ (z ◇ w))) (x ◇ (z ◇ w)) w
  have e21 := h (z ◇ (x ◇ (z ◇ w))) (z ◇ (x ◇ (z ◇ w))) y
  have e22 := h (z ◇ (x ◇ (z ◇ w))) (z ◇ (x ◇ (z ◇ w))) w
  grind

/- evaluation_normal_0104: eq2245 → eq4068 -/
