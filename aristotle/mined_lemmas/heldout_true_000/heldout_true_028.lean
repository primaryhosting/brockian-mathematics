import Mathlib

class Magma (G : Type _) where op : G → G → G
infixl:65 " ◇ " => Magma.op

/- heldout_true_000: eq2537 → eq1262 -/

theorem heldout_true_028 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G) (w : G), x = (y ◇ y) ◇ (z ◇ (y ◇ w)))
    : ∀ (x : G) (y : G) (z : G) (w : G), x = (((x ◇ x) ◇ y) ◇ z) ◇ w := by
  intro x y z w
  exact (Eq.trans (h x x x x) (h ((((x ◇ x) ◇ y) ◇ z) ◇ w) x x x).symm)

/- heldout_true_029: eq1187 → eq1180 -/
