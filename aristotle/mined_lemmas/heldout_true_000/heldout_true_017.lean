import Mathlib

class Magma (G : Type _) where op : G → G → G
infixl:65 " ◇ " => Magma.op

/- heldout_true_000: eq2537 → eq1262 -/

theorem heldout_true_017 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G) (w : G) (u : G) (v : G), x = y ◇ (z ◇ (w ◇ (u ◇ v))))
    : ∀ (x : G) (y : G) (z : G), x = (y ◇ y) ◇ (x ◇ (z ◇ x)) := by
  intro x y z
  exact (Eq.trans (h x x x x x x) (h ((y ◇ y) ◇ (x ◇ (z ◇ x))) x x x x x).symm)

/- heldout_true_018: eq1959 → eq4386 -/
