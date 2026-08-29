import Mathlib

class Magma (G : Type _) where op : G → G → G
infixl:65 " ◇ " => Magma.op

/- heldout_true_000: eq2537 → eq1262 -/

theorem heldout_true_030 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G), x = (((x ◇ y) ◇ x) ◇ y) ◇ z)
    : ∀ (x : G) (y : G) (z : G), x = (((x ◇ y) ◇ y) ◇ z) ◇ x := by
  intro x y z
  have lem2 : ∀ (X Y W Z : G), ((X ◇ Y) ◇ W) = ((X ◇ Y) ◇ Z) := fun X Y W Z => (Eq.trans (congrArg (fun t => t ◇ W) (congrArg (fun t => t ◇ Y) (h X Y ((X ◇ Y) ◇ X)))) (Eq.trans (h ((X ◇ Y) ◇ X) Y W).symm (Eq.trans (h ((X ◇ Y) ◇ X) Y Z) (congrArg (fun t => t ◇ Z) (congrArg (fun t => t ◇ Y) (h X Y ((X ◇ Y) ◇ X)).symm)))))
  exact (Eq.trans (h x y x) (Eq.trans (congrArg (fun t => t ◇ x) (lem2 (x ◇ y) x z y).symm) (Eq.trans (congrArg (fun t => t ◇ x) (congrArg (fun t => t ◇ z) (congrArg (fun t => t ◇ x) (h (x ◇ y) x x)))) (Eq.trans (congrArg (fun t => t ◇ x) (congrArg (fun t => t ◇ z) (lem2 ((((x ◇ y) ◇ x) ◇ (x ◇ y)) ◇ x) x y x).symm)) (congrArg (fun t => t ◇ x) (congrArg (fun t => t ◇ z) (congrArg (fun t => t ◇ y) (h (x ◇ y) x x).symm)))))))

/- heldout_true_031: eq1283 → eq631 -/
