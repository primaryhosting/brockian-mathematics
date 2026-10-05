import Mathlib

class Magma (G : Type _) where op : G → G → G
infixl:65 " ◇ " => Magma.op

/- heldout_true_000: eq2537 → eq1262 -/

theorem heldout_true_047 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x = (((y ◇ z) ◇ z) ◇ w) ◇ u)
    : ∀ (x : G) (y : G) (z : G) (w : G), x = ((x ◇ (y ◇ z)) ◇ w) ◇ w := by
  intro x y z w
  exact (Eq.trans (h x x x x x) (h (((x ◇ (y ◇ z)) ◇ w) ◇ w) x x x x).symm)

/- heldout_true_048: eq3251 → eq4639 -/
