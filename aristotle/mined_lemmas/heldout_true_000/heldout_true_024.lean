import Mathlib

class Magma (G : Type _) where op : G → G → G
infixl:65 " ◇ " => Magma.op

/- heldout_true_000: eq2537 → eq1262 -/

theorem heldout_true_024 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G), x = (y ◇ z) ◇ (x ◇ (x ◇ z)))
    : ∀ (x : G) (y : G), x = ((y ◇ y) ◇ x) ◇ (y ◇ x) := by
  intro x y
  have lem2 : ∀ (X Y Z : G), ((X ◇ ((Y ◇ Z) ◇ Z)) ◇ (Y ◇ Z)) = (Y ◇ Z) := fun X Y Z => (Eq.trans (congrArg (fun t => (X ◇ ((Y ◇ Z) ◇ Z)) ◇ t) (h (Y ◇ Z) Y Z)) (h (Y ◇ Z) X ((Y ◇ Z) ◇ Z)).symm)
  have lem3 : ∀ (W Y Z X : G), ((W ◇ (Y ◇ Z)) ◇ (Y ◇ Z)) = (X ◇ ((Y ◇ Z) ◇ Z)) := fun W Y Z X => (Eq.trans (congrArg (fun t => (W ◇ (Y ◇ Z)) ◇ t) (lem2 X Y Z).symm) (Eq.trans (congrArg (fun t => (W ◇ (Y ◇ Z)) ◇ t) (congrArg (fun t => (X ◇ ((Y ◇ Z) ◇ Z)) ◇ t) (lem2 X Y Z).symm)) (h (X ◇ ((Y ◇ Z) ◇ Z)) W (Y ◇ Z)).symm))
  have lem4 : ∀ (X Y Z : G), ((X ◇ (Y ◇ Z)) ◇ (Y ◇ Z)) = (Y ◇ Z) := fun X Y Z => (Eq.trans (lem3 X Y Z x) (Eq.trans (h (x ◇ ((Y ◇ Z) ◇ Z)) (x ◇ (Y ◇ Z)) (Y ◇ Z)) (Eq.trans (congrArg (fun t => ((x ◇ (Y ◇ Z)) ◇ (Y ◇ Z)) ◇ t) (congrArg (fun t => (x ◇ ((Y ◇ Z) ◇ Z)) ◇ t) (lem2 x Y Z))) (Eq.trans (congrArg (fun t => ((x ◇ (Y ◇ Z)) ◇ (Y ◇ Z)) ◇ t) (lem2 x Y Z)) (Eq.trans (congrArg (fun t => t ◇ (Y ◇ Z)) (lem3 x Y Z x)) (lem2 x Y Z))))))
  have lem5 : ∀ (Z X Y : G), (Z ◇ (X ◇ Y)) = (X ◇ Y) := fun Z X Y => (Eq.trans (h (Z ◇ (X ◇ Y)) x (X ◇ Y)) (Eq.trans (congrArg (fun t => (x ◇ (X ◇ Y)) ◇ t) (congrArg (fun t => (Z ◇ (X ◇ Y)) ◇ t) (lem4 Z X Y))) (Eq.trans (congrArg (fun t => (x ◇ (X ◇ Y)) ◇ t) (lem4 Z X Y)) (lem4 x X Y))))
  have lem6 : ∀ (X Y Z W V : G), ((X ◇ (Y ◇ Z)) ◇ (W ◇ (Y ◇ Z))) = (V ◇ (Y ◇ Z)) := fun X Y Z W V => (Eq.trans (congrArg (fun t => t ◇ (W ◇ (Y ◇ Z))) (lem5 X Y Z)) (Eq.trans (congrArg (fun t => (Y ◇ Z) ◇ t) (lem5 W Y Z)) (Eq.trans (congrArg (fun t => t ◇ (Y ◇ Z)) (lem2 x Y Z).symm) (Eq.trans (lem4 (x ◇ ((Y ◇ Z) ◇ Z)) Y Z) (lem5 V Y Z).symm))))
  have lem7 : ∀ (X Y Z W V U : G), ((X ◇ (Y ◇ (Z ◇ W))) ◇ (V ◇ (Z ◇ W))) = (U ◇ (Z ◇ W)) := fun X Y Z W V U => (Eq.trans (congrArg (fun t => (X ◇ (Y ◇ (Z ◇ W))) ◇ t) (lem6 U Z W x V).symm) (Eq.trans (congrArg (fun t => (X ◇ (Y ◇ (Z ◇ W))) ◇ t) (congrArg (fun t => (U ◇ (Z ◇ W)) ◇ t) (lem6 U Z W Y x).symm)) (h (U ◇ (Z ◇ W)) X (Y ◇ (Z ◇ W))).symm))
  have lem8 : ∀ (X Y Z W V : G), (X ◇ (Y ◇ (Z ◇ W))) = (V ◇ (Z ◇ W)) := fun X Y Z W V => (Eq.trans (h (X ◇ (Y ◇ (Z ◇ W))) x (x ◇ (Z ◇ W))) (Eq.trans (congrArg (fun t => (x ◇ (x ◇ (Z ◇ W))) ◇ t) (congrArg (fun t => (X ◇ (Y ◇ (Z ◇ W))) ◇ t) (lem7 X Y Z W x x))) (Eq.trans (congrArg (fun t => (x ◇ (x ◇ (Z ◇ W))) ◇ t) (lem7 X Y Z W x x)) (lem7 x x Z W x V))))
  exact (Eq.trans (h x x (x ◇ (y ◇ x))) (Eq.trans (congrArg (fun t => t ◇ (x ◇ (x ◇ (x ◇ (y ◇ x))))) (lem8 x x y x x)) (Eq.trans (congrArg (fun t => (x ◇ (y ◇ x)) ◇ t) (congrArg (fun t => x ◇ t) (lem8 x x y x x))) (Eq.trans (congrArg (fun t => (x ◇ (y ◇ x)) ◇ t) (lem8 x x y x x)) (lem6 x y x x ((y ◇ y) ◇ x))))))

/- heldout_true_025: eq937 → eq151 -/
