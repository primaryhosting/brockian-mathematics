import Mathlib

class Magma (G : Type _) where op : G → G → G
infixl:65 " ◇ " => Magma.op

/- heldout_true_000: eq2537 → eq1262 -/

theorem heldout_true_014 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = z ◇ ((x ◇ y) ◇ w))
    : ∀ (x : G) (y : G) (z : G), x ◇ (y ◇ z) = (x ◇ y) ◇ y := by
  intro x y z
  exact (Eq.trans (congrArg (fun t => x ◇ t) (h y z ((x ◇ y) ◇ y) x)) (h (x ◇ y) y x ((y ◇ z) ◇ x)).symm)

/- heldout_true_015: eq239 → eq3014 -/
