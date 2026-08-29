import Mathlib

class Magma (G : Type _) where op : G → G → G
infixl:65 " ◇ " => Magma.op

/- heldout_true_000: eq2537 → eq1262 -/

theorem heldout_true_000 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G), x = (y ◇ ((y ◇ x) ◇ z)) ◇ y)
    : ∀ (x : G) (y : G) (z : G), x = x ◇ (((y ◇ z) ◇ y) ◇ x) := by
  intro x y z
  exact (Eq.trans (h x ((x ◇ (((y ◇ z) ◇ y) ◇ x)) ◇ x) x) (Eq.trans (congrArg (fun t => t ◇ ((x ◇ (((y ◇ z) ◇ y) ◇ x)) ◇ x)) (congrArg (fun t => ((x ◇ (((y ◇ z) ◇ y) ◇ x)) ◇ x) ◇ t) (congrArg (fun t => t ◇ x) (h (((x ◇ (((y ◇ z) ◇ y) ◇ x)) ◇ x) ◇ x) (x ◇ (((y ◇ z) ◇ y) ◇ x)) (x ◇ (((y ◇ z) ◇ y) ◇ x)))))) (Eq.trans (congrArg (fun t => t ◇ ((x ◇ (((y ◇ z) ◇ y) ◇ x)) ◇ x)) (congrArg (fun t => ((x ◇ (((y ◇ z) ◇ y) ◇ x)) ◇ x) ◇ t) (congrArg (fun t => t ◇ x) (congrArg (fun t => t ◇ (x ◇ (((y ◇ z) ◇ y) ◇ x))) (congrArg (fun t => (x ◇ (((y ◇ z) ◇ y) ◇ x)) ◇ t) (h x (x ◇ (((y ◇ z) ◇ y) ◇ x)) x).symm))))) (h (x ◇ (((y ◇ z) ◇ y) ◇ x)) ((x ◇ (((y ◇ z) ◇ y) ◇ x)) ◇ x) x).symm)))

/- heldout_true_001: eq3244 → eq579 -/
