import Mathlib

class Magma (G : Type _) where op : G → G → G
infixl:65 " ◇ " => Magma.op

/- evaluation_normal_0100: eq2136 → eq4498 -/

theorem evaluation_normal_0168 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G) (w : G), x = (y ◇ (z ◇ w)) ◇ (z ◇ y))
    : ∀ (x : G) (y : G) (z : G), x = (y ◇ y) ◇ ((z ◇ y) ◇ y) :=
  fun x y z => (h x x x x).trans (h ((y ◇ y) ◇ ((z ◇ y) ◇ y)) x x x).symm

/- evaluation_normal_0184: eq2615 → eq4173 -/
