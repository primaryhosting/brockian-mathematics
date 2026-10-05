import Mathlib

class Magma (G : Type _) where op : G → G → G
infixl:65 " ◇ " => Magma.op

/- heldout_true_000: eq2537 → eq1262 -/

theorem heldout_true_026 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G), x = y ◇ ((z ◇ (y ◇ y)) ◇ y))
    : ∀ (x : G) (y : G), x = y ◇ ((y ◇ x) ◇ (y ◇ y)) := by
  intro x y
  exact (Eq.trans (h x x x) (h (y ◇ ((y ◇ x) ◇ (y ◇ y))) x x).symm)

/- heldout_true_027: eq2593 → eq3990 -/
