import Mathlib

class Magma (G : Type _) where op : G → G → G
infixl:65 " ◇ " => Magma.op

/- heldout_true_000: eq2537 → eq1262 -/

theorem heldout_true_016 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G) (w : G), x = y ◇ ((z ◇ z) ◇ (w ◇ w)))
    : ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = ((z ◇ y) ◇ w) ◇ z := by
  intro x y z w
  exact (Eq.trans (h (x ◇ y) x x x) (h (((z ◇ y) ◇ w) ◇ z) x x x).symm)

/- heldout_true_017: eq613 → eq1521 -/
