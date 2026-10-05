import Mathlib

class Magma (G : Type _) where op : G → G → G
infixl:65 " ◇ " => Magma.op

/- heldout_true_000: eq2537 → eq1262 -/

theorem heldout_true_031 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G), x = y ◇ (((x ◇ x) ◇ z) ◇ z))
    : ∀ (x : G) (y : G) (z : G), x = x ◇ (y ◇ ((x ◇ x) ◇ z)) := by
  intro x y z
  exact (Eq.trans (h x x ((((y ◇ ((x ◇ x) ◇ z)) ◇ (y ◇ ((x ◇ x) ◇ z))) ◇ x) ◇ x)) (congrArg (fun t => x ◇ t) (h (y ◇ ((x ◇ x) ◇ z)) ((x ◇ x) ◇ ((((y ◇ ((x ◇ x) ◇ z)) ◇ (y ◇ ((x ◇ x) ◇ z))) ◇ x) ◇ x)) x).symm))

/- heldout_true_032: eq2796 → eq3509 -/
