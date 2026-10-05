import Mathlib

class Magma (G : Type _) where op : G → G → G
infixl:65 " ◇ " => Magma.op

/- heldout_true_000: eq2537 → eq1262 -/

theorem heldout_true_046 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x = (y ◇ z) ◇ (w ◇ (w ◇ u)))
    : ∀ (x : G) (y : G) (z : G), x = (y ◇ z) ◇ ((x ◇ x) ◇ y) := by
  intro x y z
  exact (Eq.trans (h x x x x x) (h ((y ◇ z) ◇ ((x ◇ x) ◇ y)) x x x x).symm)

/- heldout_true_047: eq3226 → eq2897 -/
