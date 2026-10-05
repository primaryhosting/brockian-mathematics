import Mathlib

class Magma (G : Type _) where op : G → G → G
infixl:65 " ◇ " => Magma.op

/- heldout_true_000: eq2537 → eq1262 -/

theorem heldout_true_011 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G), x = (y ◇ z) ◇ ((z ◇ y) ◇ z))
    : ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = (x ◇ y) ◇ (z ◇ w) := by
  intro x y z w
  exact (Eq.trans (h (x ◇ y) x x) (h ((x ◇ y) ◇ (z ◇ w)) x x).symm)

/- heldout_true_012: eq189 → eq3385 -/
