import Mathlib

class Magma (G : Type _) where op : G → G → G
infixl:65 " ◇ " => Magma.op

/- heldout_true_000: eq2537 → eq1262 -/

theorem heldout_true_029 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G) (w : G), x = y ◇ ((z ◇ (z ◇ y)) ◇ w))
    : ∀ (x : G) (y : G) (z : G), x = y ◇ ((z ◇ (z ◇ x)) ◇ x) := by
  intro x y z
  exact (Eq.trans (h x x x x) (h (y ◇ ((z ◇ (z ◇ x)) ◇ x)) x x x).symm)

/- heldout_true_030: eq3070 → eq3081 -/
