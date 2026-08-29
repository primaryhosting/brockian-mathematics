import Mathlib

class Magma (G : Type _) where op : G → G → G
infixl:65 " ◇ " => Magma.op

/- heldout_true_000: eq2537 → eq1262 -/

theorem heldout_true_003 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G), x = y ◇ ((z ◇ (y ◇ z)) ◇ y))
    : ∀ (x : G) (y : G) (z : G), x = ((x ◇ y) ◇ x) ◇ z := by
  intro x y z
  exact (Eq.trans (h x x x) (h (((x ◇ y) ◇ x) ◇ z) x x).symm)

/- heldout_true_004: eq1982 → eq4336 -/
