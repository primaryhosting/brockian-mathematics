import Mathlib

class Magma (G : Type _) where op : G → G → G
infixl:65 " ◇ " => Magma.op

/- heldout_true_000: eq2537 → eq1262 -/

theorem heldout_true_008 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x = ((y ◇ x) ◇ z) ◇ (w ◇ u))
    : ∀ (x : G) (y : G) (z : G), x = y ◇ (((z ◇ z) ◇ x) ◇ x) := by
  intro x y z
  exact (Eq.trans (h x (x ◇ y) (x ◇ x) ((z ◇ z) ◇ x) x) (congrArg (fun t => t ◇ (((z ◇ z) ◇ x) ◇ x)) (h y x x x x).symm))

/- heldout_true_009: eq1997 → eq3701 -/
