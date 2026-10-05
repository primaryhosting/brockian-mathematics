import Mathlib

class Magma (G : Type _) where op : G → G → G
infixl:65 " ◇ " => Magma.op

/- heldout_true_000: eq2537 → eq1262 -/

theorem heldout_true_015 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G), x = (y ◇ (z ◇ x)) ◇ y)
    : ∀ (x : G) (y : G) (z : G) (w : G), x = ((y ◇ (z ◇ z)) ◇ y) ◇ w := by
  intro x y z w
  exact (Eq.trans (h x x (x ◇ (x ◇ x))) (Eq.trans (congrArg (fun t => t ◇ x) (congrArg (fun t => x ◇ t) (h x x x).symm)) (Eq.trans (congrArg (fun t => t ◇ x) (congrArg (fun t => x ◇ t) (h x (((y ◇ (z ◇ z)) ◇ y) ◇ w) x))) (h (((y ◇ (z ◇ z)) ◇ y) ◇ w) x ((((y ◇ (z ◇ z)) ◇ y) ◇ w) ◇ (x ◇ x))).symm)))

/- heldout_true_016: eq992 → eq4222 -/
