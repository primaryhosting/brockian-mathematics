import Mathlib

class Magma (G : Type _) where op : G → G → G
infixl:65 " ◇ " => Magma.op

/- heldout_true_000: eq2537 → eq1262 -/

theorem heldout_true_044 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G) (w : G), x = y ◇ (z ◇ (w ◇ (z ◇ y))))
    : ∀ (x : G) (y : G), x = ((y ◇ x) ◇ (x ◇ x)) ◇ x := by
  intro x y
  exact (Eq.trans (h x x x x) (h (((y ◇ x) ◇ (x ◇ x)) ◇ x) x x x).symm)

/- heldout_true_045: eq3856 → eq3688 -/
