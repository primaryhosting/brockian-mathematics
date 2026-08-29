import Mathlib

class Magma (G : Type _) where op : G → G → G
infixl:65 " ◇ " => Magma.op

/- heldout_true_000: eq2537 → eq1262 -/

theorem heldout_true_007 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = (z ◇ (w ◇ w)) ◇ x)
    : ∀ (x : G) (y : G) (z : G), x ◇ y = (z ◇ y) ◇ (x ◇ x) := by
  intro x y z
  exact (Eq.trans (h x y x x) (Eq.trans (h (x ◇ (x ◇ x)) x x x) (Eq.trans (h (x ◇ (x ◇ x)) (z ◇ y) x x).symm (h (z ◇ y) (x ◇ x) x x).symm)))

/- heldout_true_008: eq2123 → eq1383 -/
