import Mathlib

class Magma (G : Type _) where op : G → G → G
infixl:65 " ◇ " => Magma.op

/- heldout_true_000: eq2537 → eq1262 -/

theorem heldout_true_002 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G) (w : G), x = y ◇ ((z ◇ y) ◇ (z ◇ w)))
    : ∀ (x : G) (y : G) (z : G), x = y ◇ (z ◇ ((y ◇ x) ◇ z)) := by
  intro x y z
  exact (Eq.trans (h x x x x) (h (y ◇ (z ◇ ((y ◇ x) ◇ z))) x x x).symm)

/- heldout_true_003: eq1172 → eq262 -/
