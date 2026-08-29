import Mathlib

class Magma (G : Type _) where op : G → G → G
infixl:65 " ◇ " => Magma.op

/- heldout_true_000: eq2537 → eq1262 -/

theorem heldout_true_039 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G) (w : G), x = y ◇ (z ◇ (w ◇ x)))
    : ∀ (x : G) (y : G), x = y ◇ (y ◇ ((y ◇ x) ◇ x)) := by
  intro x y
  exact (h x y y (y ◇ x))

/- heldout_true_040: eq4188 → eq332 -/
