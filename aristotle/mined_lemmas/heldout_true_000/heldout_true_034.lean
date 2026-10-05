import Mathlib

class Magma (G : Type _) where op : G → G → G
infixl:65 " ◇ " => Magma.op

/- heldout_true_000: eq2537 → eq1262 -/

theorem heldout_true_034 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G), x = ((y ◇ x) ◇ x) ◇ z)
    : ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x ◇ x = (y ◇ z) ◇ (w ◇ u) := by
  intro x y z w u
  have lem2 : ∀ (X Y : G), (X ◇ Y) = X := fun X Y => (Eq.trans (congrArg (fun t => t ◇ Y) (h X x X)) (h X (x ◇ X) Y).symm)
  exact (Eq.trans (lem2 (x ◇ x) ((y ◇ z) ◇ (w ◇ u))).symm (Eq.trans (congrArg (fun t => t ◇ ((y ◇ z) ◇ (w ◇ u))) (lem2 (x ◇ x) ((y ◇ z) ◇ (w ◇ u))).symm) (Eq.trans (lem2 (((x ◇ x) ◇ ((y ◇ z) ◇ (w ◇ u))) ◇ ((y ◇ z) ◇ (w ◇ u))) x).symm (h ((y ◇ z) ◇ (w ◇ u)) (x ◇ x) x).symm)))

/- heldout_true_035: eq2377 → eq446 -/
