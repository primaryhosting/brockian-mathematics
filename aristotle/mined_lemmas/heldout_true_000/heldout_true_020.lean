import Mathlib

class Magma (G : Type _) where op : G → G → G
infixl:65 " ◇ " => Magma.op

/- heldout_true_000: eq2537 → eq1262 -/

theorem heldout_true_020 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G), x = ((y ◇ (y ◇ z)) ◇ z) ◇ z)
    : ∀ (x : G) (y : G) (z : G), x = (y ◇ y) ◇ (y ◇ z) := by
  intro x y z
  exact (Eq.trans (h x x x) (h ((y ◇ y) ◇ (y ◇ z)) x x).symm)

/- heldout_true_021: eq98 → eq3482 -/
