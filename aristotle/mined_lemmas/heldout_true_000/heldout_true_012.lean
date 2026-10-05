import Mathlib

class Magma (G : Type _) where op : G → G → G
infixl:65 " ◇ " => Magma.op

/- heldout_true_000: eq2537 → eq1262 -/

theorem heldout_true_012 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G) (w : G), x = (y ◇ z) ◇ (x ◇ w))
    : ∀ (x : G) (y : G) (z : G), x ◇ y = z ◇ (x ◇ (y ◇ z)) := by
  intro x y z
  have lem2 : ∀ (X Y Z : G), (X ◇ (Y ◇ Z)) = Y := fun X Y Z => (Eq.trans (congrArg (fun t => t ◇ (Y ◇ Z)) (h X x x x)) (h Y (x ◇ x) (X ◇ x) Z).symm)
  exact (Eq.trans (congrArg (fun t => x ◇ t) (lem2 (z ◇ (x ◇ (y ◇ z))) y x).symm) (lem2 x (z ◇ (x ◇ (y ◇ z))) (y ◇ x)))

/- heldout_true_013: eq2166 → eq906 -/
