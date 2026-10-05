import Mathlib

class Magma (G : Type _) where op : G → G → G
infixl:65 " ◇ " => Magma.op

/- heldout_true_000: eq2537 → eq1262 -/

theorem heldout_true_022 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G), x = ((y ◇ z) ◇ z) ◇ (y ◇ z))
    : ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x = y ◇ ((z ◇ (w ◇ x)) ◇ u) := by
  intro x y z w u
  exact (Eq.trans (h x x x) (h (y ◇ ((z ◇ (w ◇ x)) ◇ u)) x x).symm)

/- heldout_true_023: eq1748 → eq4204 -/
