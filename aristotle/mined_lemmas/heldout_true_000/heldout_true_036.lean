import Mathlib

class Magma (G : Type _) where op : G → G → G
infixl:65 " ◇ " => Magma.op

/- heldout_true_000: eq2537 → eq1262 -/

theorem heldout_true_036 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G), x = ((x ◇ y) ◇ x) ◇ (z ◇ y))
    : ∀ (x : G) (y : G) (z : G), (x ◇ x) ◇ x = (x ◇ y) ◇ z := by
  intro x y z
  have lem2 : ∀ (X Z Y : G), (X ◇ Z) = (X ◇ Y) := fun X Z Y => (Eq.trans (h (X ◇ Z) X x) (Eq.trans (congrArg (fun t => t ◇ (x ◇ X)) (h X Z X).symm) (Eq.trans (congrArg (fun t => t ◇ (x ◇ X)) (h X Y X)) (h (X ◇ Y) X x).symm)))
  exact (Eq.trans (congrArg (fun t => t ◇ x) (lem2 x x y)) (lem2 (x ◇ y) x z))

/- heldout_true_037: eq1367 → eq365 -/
