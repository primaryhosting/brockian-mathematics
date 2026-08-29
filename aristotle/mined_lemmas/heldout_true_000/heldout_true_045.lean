import Mathlib

class Magma (G : Type _) where op : G → G → G
infixl:65 " ◇ " => Magma.op

/- heldout_true_000: eq2537 → eq1262 -/

theorem heldout_true_045 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x ◇ y = (z ◇ w) ◇ (u ◇ x))
    : ∀ (x : G) (y : G), x ◇ x = (y ◇ y) ◇ (y ◇ y) := by
  intro x y
  exact (Eq.trans (h x x (x ◇ x) (x ◇ y) x) (Eq.trans (h ((x ◇ x) ◇ (x ◇ y)) (x ◇ x) x x x) (Eq.trans (h ((x ◇ x) ◇ (x ◇ y)) (y ◇ y) x x x).symm (congrArg (fun t => t ◇ (y ◇ y)) (h y y x x x).symm))))

/- heldout_true_046: eq1622 → eq1756 -/
