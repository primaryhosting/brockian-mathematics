import Mathlib

class Magma (G : Type _) where op : G → G → G
infixl:65 " ◇ " => Magma.op

/- evaluation_normal_0100: eq2136 → eq4498 -/

theorem evaluation_normal_0184 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G) (w : G), x = (y ◇ ((z ◇ z) ◇ w)) ◇ z)
    : ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = ((y ◇ y) ◇ z) ◇ w :=
  fun x y z w => (h (x ◇ y) x x x).trans (h (((y ◇ y) ◇ z) ◇ w) x x x).symm

/- evaluation_normal_0038: eq2936 → eq23 -/
