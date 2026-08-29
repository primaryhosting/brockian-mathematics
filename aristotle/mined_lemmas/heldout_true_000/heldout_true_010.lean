import Mathlib

class Magma (G : Type _) where op : G → G → G
infixl:65 " ◇ " => Magma.op

/- heldout_true_000: eq2537 → eq1262 -/

theorem heldout_true_010 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G) (w : G), x = ((y ◇ (y ◇ z)) ◇ w) ◇ y)
    : ∀ (x : G) (y : G) (z : G), x ◇ x = x ◇ ((y ◇ z) ◇ z) := by
  intro x y z
  exact (Eq.trans (h (x ◇ x) x x x) (h (x ◇ ((y ◇ z) ◇ z)) x x x).symm)

/- heldout_true_011: eq1795 → eq3730 -/
