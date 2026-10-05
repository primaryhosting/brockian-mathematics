import Mathlib

class Magma (G : Type _) where op : G → G → G
infixl:65 " ◇ " => Magma.op

/- heldout_true_000: eq2537 → eq1262 -/

theorem heldout_true_019 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x = y ◇ (z ◇ ((w ◇ y) ◇ u)))
    : ∀ (x : G) (y : G), x ◇ (x ◇ x) = (y ◇ y) ◇ x := by
  intro x y
  exact (Eq.trans (h (x ◇ (x ◇ x)) x x x x) (h ((y ◇ y) ◇ x) x x x x).symm)

/- heldout_true_020: eq2966 → eq181 -/
