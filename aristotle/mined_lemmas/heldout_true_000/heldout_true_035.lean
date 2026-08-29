import Mathlib

class Magma (G : Type _) where op : G → G → G
infixl:65 " ◇ " => Magma.op

/- heldout_true_000: eq2537 → eq1262 -/

theorem heldout_true_035 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G) (w : G), x = (y ◇ (z ◇ (x ◇ w))) ◇ y)
    : ∀ (x : G) (y : G) (z : G), x = x ◇ (y ◇ (z ◇ (x ◇ x))) := by
  intro x y z
  exact (Eq.trans (h x x ((x ◇ x) ◇ (x ◇ (x ◇ x))) x) (Eq.trans (congrArg (fun t => t ◇ x) (congrArg (fun t => x ◇ t) (h x (x ◇ x) x x).symm)) (Eq.trans (congrArg (fun t => t ◇ x) (congrArg (fun t => x ◇ t) (h x ((x ◇ (y ◇ (z ◇ (x ◇ x)))) ◇ x) x x))) (h (x ◇ (y ◇ (z ◇ (x ◇ x)))) x (((x ◇ (y ◇ (z ◇ (x ◇ x)))) ◇ x) ◇ (x ◇ (x ◇ x))) x).symm)))

/- heldout_true_036: eq2057 → eq4586 -/
