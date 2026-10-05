import Mathlib

class Magma (G : Type _) where op : G → G → G
infixl:65 " ◇ " => Magma.op

/- heldout_true_000: eq2537 → eq1262 -/

theorem heldout_true_037 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G), x = y ◇ (((z ◇ y) ◇ x) ◇ y))
    : ∀ (x : G) (y : G), x ◇ x = (y ◇ x) ◇ y := by
  intro x y
  have lem2 : ∀ (X Y Z : G), ((X ◇ Y) ◇ (Y ◇ (Z ◇ Y))) = Z := fun X Y Z => (Eq.trans (congrArg (fun t => (X ◇ Y) ◇ t) (congrArg (fun t => Y ◇ t) (congrArg (fun t => t ◇ Y) (h Z (X ◇ Y) x)))) (Eq.trans (congrArg (fun t => (X ◇ Y) ◇ t) (h (((x ◇ (X ◇ Y)) ◇ Z) ◇ (X ◇ Y)) Y X).symm) (h Z (X ◇ Y) x).symm))
  exact (Eq.trans (lem2 x x (x ◇ x)).symm (Eq.trans (congrArg (fun t => (x ◇ x) ◇ t) (congrArg (fun t => x ◇ t) (lem2 x x ((x ◇ x) ◇ x)).symm)) (Eq.trans (congrArg (fun t => (x ◇ x) ◇ t) (congrArg (fun t => x ◇ t) (congrArg (fun t => (x ◇ x) ◇ t) (congrArg (fun t => x ◇ t) (congrArg (fun t => ((x ◇ x) ◇ x) ◇ t) (h x x ((y ◇ x) ◇ y))))))) (Eq.trans (congrArg (fun t => (x ◇ x) ◇ t) (congrArg (fun t => x ◇ t) (congrArg (fun t => (x ◇ x) ◇ t) (congrArg (fun t => x ◇ t) (lem2 (x ◇ x) x ((((y ◇ x) ◇ y) ◇ x) ◇ x)))))) (Eq.trans (congrArg (fun t => (x ◇ x) ◇ t) (congrArg (fun t => x ◇ t) (lem2 x x (((y ◇ x) ◇ y) ◇ x)))) (lem2 x x ((y ◇ x) ◇ y)))))))

/- heldout_true_038: eq1619 → eq809 -/
