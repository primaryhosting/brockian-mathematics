import Mathlib

class Magma (G : Type _) where op : G → G → G
infixl:65 " ◇ " => Magma.op

/- heldout_true_000: eq2537 → eq1262 -/

theorem heldout_true_038 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G) (w : G), x = (y ◇ z) ◇ (w ◇ (w ◇ y)))
    : ∀ (x : G) (y : G) (z : G) (w : G), x = y ◇ (z ◇ ((w ◇ w) ◇ w)) := by
  intro x y z w
  exact (Eq.trans (h x x x x) (h (y ◇ (z ◇ ((w ◇ w) ◇ w))) x x x).symm)

/- heldout_true_039: eq94 → eq713 -/
