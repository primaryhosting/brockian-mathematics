import Mathlib

class Magma (G : Type _) where op : G → G → G
infixl:65 " ◇ " => Magma.op

/- evaluation_normal_0100: eq2136 → eq4498 -/

theorem evaluation_normal_0004 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G), x = y ◇ ((z ◇ x) ◇ x))
    : ∀ (x : G) (y : G) (z : G) (w : G), x = y ◇ (((z ◇ w) ◇ x) ◇ x) :=
  fun x y z w => h x y (z ◇ w)

/- evaluation_normal_0130: eq844 → eq3725 -/
