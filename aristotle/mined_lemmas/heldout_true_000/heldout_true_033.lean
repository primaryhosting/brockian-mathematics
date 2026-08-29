import Mathlib

class Magma (G : Type _) where op : G → G → G
infixl:65 " ◇ " => Magma.op

/- heldout_true_000: eq2537 → eq1262 -/

theorem heldout_true_033 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G), x = y ◇ ((x ◇ y) ◇ (y ◇ z)))
    : ∀ (x : G) (y : G), x ◇ x = y ◇ ((x ◇ y) ◇ x) := by
  intro x y
  exact (Eq.trans (congrArg (fun t => x ◇ t) (h x ((y ◇ ((x ◇ y) ◇ x)) ◇ x) x)) (Eq.trans (congrArg (fun t => x ◇ t) (congrArg (fun t => ((y ◇ ((x ◇ y) ◇ x)) ◇ x) ◇ t) (h ((x ◇ ((y ◇ ((x ◇ y) ◇ x)) ◇ x)) ◇ (((y ◇ ((x ◇ y) ◇ x)) ◇ x) ◇ x)) x x))) (h (y ◇ ((x ◇ y) ◇ x)) x ((((x ◇ ((y ◇ ((x ◇ y) ◇ x)) ◇ x)) ◇ (((y ◇ ((x ◇ y) ◇ x)) ◇ x) ◇ x)) ◇ x) ◇ (x ◇ x))).symm))

/- heldout_true_034: eq272 → eq3710 -/
