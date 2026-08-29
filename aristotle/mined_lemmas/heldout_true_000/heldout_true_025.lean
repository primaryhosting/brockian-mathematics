import Mathlib

class Magma (G : Type _) where op : G → G → G
infixl:65 " ◇ " => Magma.op

/- heldout_true_000: eq2537 → eq1262 -/

theorem heldout_true_025 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G) (w : G), x = y ◇ ((y ◇ z) ◇ (z ◇ w)))
    : ∀ (x : G), x = (x ◇ x) ◇ (x ◇ x) := by
  intro x
  exact (Eq.trans (h x x x x) (h ((x ◇ x) ◇ (x ◇ x)) x x x).symm)

/- heldout_true_026: eq1168 → eq910 -/
