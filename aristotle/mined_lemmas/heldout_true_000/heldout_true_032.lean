import Mathlib

class Magma (G : Type _) where op : G → G → G
infixl:65 " ◇ " => Magma.op

/- heldout_true_000: eq2537 → eq1262 -/

theorem heldout_true_032 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G), x = ((y ◇ z) ◇ (y ◇ z)) ◇ y)
    : ∀ (x : G) (y : G), x ◇ y = x ◇ ((x ◇ x) ◇ y) := by
  intro x y
  exact (Eq.trans (h (x ◇ y) x x) (h (x ◇ ((x ◇ x) ◇ y)) x x).symm)

/- heldout_true_033: eq884 → eq3474 -/
