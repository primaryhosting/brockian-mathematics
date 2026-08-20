import Mathlib.Tactic

set_option quotPrecheck false
class Magma (G : Type _) where op : G → G → G
infixl:65 " ◇ " => Magma.op


-- Problem normal_0355: eq899 → eq4591

theorem problem_normal_0365 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G), x = y ◇ (((z ◇ x) ◇ x) ◇ z))
    : ∀ (x : G) (y : G) (z : G), x = (x ◇ ((y ◇ x) ◇ y)) ◇ z := by
  intro x y z;
  convert h x _ _ using 1;
  convert rfl;
  swap;
  exact ( ‹Magma G›.op ( ‹Magma G›.op ( ‹Magma G›.op z x ) x ) z );
  grind +splitIndPred

-- Problem normal_0366: eq1919 → eq4233
