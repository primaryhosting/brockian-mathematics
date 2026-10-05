import Mathlib

class Magma (G : Type _) where op : G → G → G
infixl:65 " ◇ " => Magma.op

/- heldout_true_000: eq2537 → eq1262 -/

theorem heldout_true_041 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G), x = y ◇ ((y ◇ y) ◇ (x ◇ z)))
    : ∀ (x : G) (y : G) (z : G), x ◇ y = (z ◇ (y ◇ z)) ◇ y := by
  intro x y z
  exact (Eq.trans (h (x ◇ y) x x) (Eq.trans (congrArg (fun t => x ◇ t) (h ((x ◇ x) ◇ ((x ◇ y) ◇ x)) (x ◇ x) x)) (Eq.trans (h ((x ◇ x) ◇ (x ◇ x)) x (((x ◇ x) ◇ ((x ◇ y) ◇ x)) ◇ x)).symm (Eq.trans (h ((x ◇ x) ◇ (x ◇ x)) x (((x ◇ x) ◇ (((z ◇ (y ◇ z)) ◇ y) ◇ x)) ◇ x)) (Eq.trans (congrArg (fun t => x ◇ t) (h ((x ◇ x) ◇ (((z ◇ (y ◇ z)) ◇ y) ◇ x)) (x ◇ x) x).symm) (h ((z ◇ (y ◇ z)) ◇ y) x x).symm)))))

/- heldout_true_042: eq2209 → eq1048 -/
