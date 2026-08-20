import Mathlib.Tactic

set_option quotPrecheck false
class Magma (G : Type _) where op : G → G → G
infixl:65 " ◇ " => Magma.op


-- Problem normal_0355: eq899 → eq4591

theorem problem_normal_0414 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G), x = (x ◇ x) ◇ (y ◇ (x ◇ z)))
    : ∀ (x : G) (y : G) (z : G), x = (x ◇ (y ◇ y)) ◇ (x ◇ z) := by
  intro x y z;
  convert h x _ z using 1;
  swap;
  bv_omega;
  grind

-- Problem normal_0422: eq2170 → eq4640
