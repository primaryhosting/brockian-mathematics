import Mathlib

class Magma (G : Type _) where op : G → G → G
infixl:65 " ◇ " => Magma.op

/- heldout_true_000: eq2537 → eq1262 -/

theorem heldout_true_048 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x = (((y ◇ z) ◇ w) ◇ u) ◇ u)
    : ∀ (x : G) (y : G) (z : G), (x ◇ y) ◇ x = (y ◇ z) ◇ y := by
  intro x y z
  exact (Eq.trans (h ((x ◇ y) ◇ x) x x x x) (h ((y ◇ z) ◇ y) x x x x).symm)

/- heldout_true_049: eq2219 → eq1221 -/
