import Mathlib

class Magma (G : Type _) where op : G → G → G
infixl:65 " ◇ " => Magma.op

/- heldout_true_000: eq2537 → eq1262 -/

theorem heldout_true_049 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G) (w : G), x = ((y ◇ z) ◇ w) ◇ (y ◇ z))
    : ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x = y ◇ ((z ◇ (w ◇ u)) ◇ u) := by
  intro x y z w u
  exact (Eq.trans (h x x x x) (h (y ◇ ((z ◇ (w ◇ u)) ◇ u)) x x x).symm)


