import Mathlib

class Magma (G : Type _) where op : G → G → G
infixl:65 " ◇ " => Magma.op

/- heldout_true_000: eq2537 → eq1262 -/

theorem heldout_true_021 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x = y ◇ (z ◇ (w ◇ u)))
    : ∀ (x : G) (y : G), x ◇ x = y ◇ ((y ◇ x) ◇ y) := by
  intro x y
  exact (Eq.trans (h (x ◇ x) x x x x) (h (y ◇ ((y ◇ x) ◇ y)) x x x x).symm)

/- heldout_true_022: eq2201 → eq1201 -/
