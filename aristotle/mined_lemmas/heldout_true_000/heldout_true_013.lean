import Mathlib

class Magma (G : Type _) where op : G → G → G
infixl:65 " ◇ " => Magma.op

/- heldout_true_000: eq2537 → eq1262 -/

theorem heldout_true_013 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G), x = ((y ◇ z) ◇ x) ◇ (y ◇ y))
    : ∀ (x : G) (y : G), x = y ◇ ((y ◇ x) ◇ (x ◇ x)) := by
  intro x y
  have lem2 : ∀ (X Y Z : G), (X ◇ ((Y ◇ Z) ◇ (Y ◇ Z))) = (Y ◇ Y) := fun X Y Z => (Eq.trans (congrArg (fun t => t ◇ ((Y ◇ Z) ◇ (Y ◇ Z))) (h X Y Z)) (h (Y ◇ Y) (Y ◇ Z) X).symm)
  exact (Eq.trans (h x (x ◇ x) x) (Eq.trans (lem2 (((x ◇ x) ◇ x) ◇ x) x x) (Eq.trans (lem2 (((x ◇ x) ◇ x) ◇ (y ◇ ((y ◇ x) ◇ (x ◇ x)))) x x).symm (h (y ◇ ((y ◇ x) ◇ (x ◇ x))) (x ◇ x) x).symm)))

/- heldout_true_014: eq3589 → eq4511 -/
