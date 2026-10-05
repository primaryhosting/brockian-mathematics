import Mathlib

class Magma (G : Type _) where op : G → G → G
infixl:65 " ◇ " => Magma.op

/- heldout_true_000: eq2537 → eq1262 -/

theorem heldout_true_018 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G), x = (y ◇ (z ◇ x)) ◇ (x ◇ y))
    : ∀ (x : G) (y : G), x ◇ (x ◇ x) = (y ◇ x) ◇ y := by
  intro x y
  have lem2 : ∀ (X Y Z : G), (X ◇ (Y ◇ (Y ◇ (Z ◇ X)))) = Y := fun X Y Z => (Eq.trans (congrArg (fun t => t ◇ (Y ◇ (Y ◇ (Z ◇ X)))) (h X Y Z)) (h Y (Y ◇ (Z ◇ X)) X).symm)
  have lem3 : ∀ (X Y : G), ((X ◇ Y) ◇ Y) = Y := fun X Y => (Eq.trans (congrArg (fun t => (X ◇ Y) ◇ t) (lem2 Y Y X).symm) (lem2 (X ◇ Y) Y Y))
  have lem4 : ∀ (X Y : G), (X ◇ (X ◇ (Y ◇ X))) = X := fun X Y => (Eq.trans (congrArg (fun t => t ◇ (X ◇ (Y ◇ X))) (lem3 Y X).symm) (Eq.trans (congrArg (fun t => t ◇ (X ◇ (Y ◇ X))) (congrArg (fun t => (Y ◇ X) ◇ t) (lem3 x X).symm)) (h X (Y ◇ X) (x ◇ X)).symm))
  have lem5 : ∀ (X : G), (X ◇ (X ◇ X)) = X := fun X => (Eq.trans (congrArg (fun t => t ◇ (X ◇ X)) (h X (X ◇ (x ◇ X)) X)) (Eq.trans (congrArg (fun t => t ◇ (X ◇ X)) (congrArg (fun t => ((X ◇ (x ◇ X)) ◇ (X ◇ X)) ◇ t) (lem4 X x))) (Eq.trans (congrArg (fun t => t ◇ (X ◇ X)) (congrArg (fun t => t ◇ X) (h X X x).symm)) (Eq.trans (congrArg (fun t => t ◇ (X ◇ X)) (congrArg (fun t => X ◇ t) (lem3 x X).symm)) (h X X (x ◇ X)).symm))))
  have lem6 : ∀ (X Y Z : G), ((X ◇ Y) ◇ (Z ◇ (Z ◇ X))) = Z := fun X Y Z => (Eq.trans (congrArg (fun t => t ◇ (Z ◇ (Z ◇ X))) (h (X ◇ Y) Z (Y ◇ (x ◇ X)))) (Eq.trans (congrArg (fun t => t ◇ (Z ◇ (Z ◇ X))) (congrArg (fun t => t ◇ ((X ◇ Y) ◇ Z)) (congrArg (fun t => Z ◇ t) (h X Y x).symm))) (h Z (Z ◇ X) (X ◇ Y)).symm))
  have lem7 : ∀ (X Y : G), (X ◇ (X ◇ Y)) = (X ◇ Y) := fun X Y => (Eq.trans (congrArg (fun t => X ◇ t) (lem6 X Y (X ◇ Y)).symm) (lem2 X (X ◇ Y) (X ◇ Y)))
  have lem8 : ∀ (X Y : G), ((X ◇ (X ◇ X)) ◇ (Y ◇ X)) = Y := fun X Y => (Eq.trans (congrArg (fun t => (X ◇ (X ◇ X)) ◇ t) (lem7 Y X).symm) (Eq.trans (congrArg (fun t => t ◇ (Y ◇ (Y ◇ X))) (lem5 X)) (Eq.trans (congrArg (fun t => X ◇ t) (congrArg (fun t => Y ◇ t) (lem7 Y X).symm)) (lem2 X Y Y))))
  have lem9 : ∀ (Y X : G), (Y ◇ (Y ◇ Y)) = (X ◇ Y) := fun Y X => (Eq.trans (lem5 Y) (Eq.trans (h Y (Y ◇ (Y ◇ Y)) X) (Eq.trans (congrArg (fun t => t ◇ (Y ◇ (Y ◇ (Y ◇ Y)))) (lem8 Y X)) (congrArg (fun t => X ◇ t) (lem4 Y Y)))))
  exact (Eq.trans (lem9 x ((y ◇ x) ◇ y)) (Eq.trans (lem6 ((y ◇ x) ◇ y) x (((y ◇ x) ◇ y) ◇ x)).symm (Eq.trans (congrArg (fun t => t ◇ ((((y ◇ x) ◇ y) ◇ x) ◇ ((((y ◇ x) ◇ y) ◇ x) ◇ ((y ◇ x) ◇ y)))) (lem9 x ((y ◇ x) ◇ y)).symm) (Eq.trans (congrArg (fun t => (x ◇ (x ◇ x)) ◇ t) (congrArg (fun t => t ◇ ((((y ◇ x) ◇ y) ◇ x) ◇ ((y ◇ x) ◇ y))) (lem7 ((y ◇ x) ◇ y) x).symm)) (Eq.trans (congrArg (fun t => (x ◇ (x ◇ x)) ◇ t) (congrArg (fun t => t ◇ ((((y ◇ x) ◇ y) ◇ x) ◇ ((y ◇ x) ◇ y))) (congrArg (fun t => ((y ◇ x) ◇ y) ◇ t) (lem7 ((y ◇ x) ◇ y) x).symm))) (Eq.trans (congrArg (fun t => (x ◇ (x ◇ x)) ◇ t) (h (((y ◇ x) ◇ y) ◇ x) ((y ◇ x) ◇ y) ((y ◇ x) ◇ y)).symm) (lem8 x ((y ◇ x) ◇ y))))))))

/- heldout_true_019: eq800 → eq4388 -/
