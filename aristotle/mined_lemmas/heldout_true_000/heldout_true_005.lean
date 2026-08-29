import Mathlib

class Magma (G : Type _) where op : G → G → G
infixl:65 " ◇ " => Magma.op

/- heldout_true_000: eq2537 → eq1262 -/

theorem heldout_true_005 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G), x = ((y ◇ x) ◇ y) ◇ (x ◇ z))
    : ∀ (x : G) (y : G) (z : G), x = x ◇ ((y ◇ x) ◇ (z ◇ x)) := by
  intro x y z
  have lem2 : ∀ (X Y : G), (X ◇ (X ◇ Y)) = X := fun X Y => (Eq.trans (congrArg (fun t => t ◇ (X ◇ Y)) (h X X X)) (h X (X ◇ X) Y).symm)
  have lem3 : ∀ (X Y : G), (X ◇ (X ◇ Y)) = (X ◇ Y) := fun X Y => (Eq.trans (congrArg (fun t => X ◇ t) (lem2 (X ◇ Y) x).symm) (Eq.trans (congrArg (fun t => t ◇ ((X ◇ Y) ◇ ((X ◇ Y) ◇ x))) (lem2 X (X ◇ x)).symm) (Eq.trans (congrArg (fun t => t ◇ ((X ◇ Y) ◇ ((X ◇ Y) ◇ x))) (congrArg (fun t => X ◇ t) (lem2 X x))) (Eq.trans (congrArg (fun t => t ◇ ((X ◇ Y) ◇ ((X ◇ Y) ◇ x))) (congrArg (fun t => t ◇ X) (lem2 X Y).symm)) (h (X ◇ Y) X ((X ◇ Y) ◇ x)).symm))))
  exact (Eq.trans (lem2 x (x ◇ ((y ◇ x) ◇ (z ◇ x)))).symm (Eq.trans (congrArg (fun t => x ◇ t) (lem3 x ((y ◇ x) ◇ (z ◇ x)))) (lem3 x ((y ◇ x) ◇ (z ◇ x)))))

/- heldout_true_006: eq1193 → eq2383 -/
