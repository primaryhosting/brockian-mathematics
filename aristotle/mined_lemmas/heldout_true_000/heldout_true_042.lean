import Mathlib

class Magma (G : Type _) where op : G → G → G
infixl:65 " ◇ " => Magma.op

/- heldout_true_000: eq2537 → eq1262 -/

theorem heldout_true_042 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G) (w : G), x = ((y ◇ z) ◇ z) ◇ (w ◇ z))
    : ∀ (x : G) (y : G), x = x ◇ ((y ◇ (y ◇ y)) ◇ x) := by
  intro x y
  exact (Eq.trans (h x x x x) (h (x ◇ ((y ◇ (y ◇ y)) ◇ x)) x x x).symm)

/- heldout_true_043: eq2529 → eq2327 -/
