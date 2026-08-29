import Mathlib

class Magma (G : Type _) where op : G → G → G
infixl:65 " ◇ " => Magma.op

/- heldout_true_000: eq2537 → eq1262 -/

theorem heldout_true_009 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G), x = (y ◇ (z ◇ z)) ◇ (y ◇ y))
    : ∀ (x : G) (y : G) (z : G) (w : G), x ◇ x = (y ◇ z) ◇ (y ◇ w) := by
  intro x y z w
  exact (Eq.trans (h (x ◇ x) x x) (h ((y ◇ z) ◇ (y ◇ w)) x x).symm)

/- heldout_true_010: eq2969 → eq3469 -/
