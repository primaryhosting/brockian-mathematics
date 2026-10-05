import Mathlib

class Magma (G : Type _) where op : G → G → G
infixl:65 " ◇ " => Magma.op

/- heldout_true_000: eq2537 → eq1262 -/

theorem heldout_true_023 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G), x = (y ◇ y) ◇ ((z ◇ z) ◇ z))
    : ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = ((z ◇ x) ◇ w) ◇ y := by
  intro x y z w
  exact (Eq.trans (h (x ◇ y) x x) (h (((z ◇ x) ◇ w) ◇ y) x x).symm)

/- heldout_true_024: eq1554 → eq2127 -/
