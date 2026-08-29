import Mathlib

class Magma (G : Type _) where op : G → G → G
infixl:65 " ◇ " => Magma.op

/- heldout_true_000: eq2537 → eq1262 -/

theorem heldout_true_043 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x = (y ◇ ((x ◇ z) ◇ w)) ◇ u)
    : ∀ (x : G) (y : G), x = (y ◇ (y ◇ (x ◇ x))) ◇ x := by
  intro x y
  exact (Eq.trans (h x (x ◇ (((y ◇ (y ◇ (x ◇ x))) ◇ x) ◇ x)) x x x) (congrArg (fun t => t ◇ x) (h (y ◇ (y ◇ (x ◇ x))) x x x ((x ◇ x) ◇ x)).symm))

/- heldout_true_044: eq599 → eq2696 -/
