import Mathlib.Tactic

set_option quotPrecheck false
class Magma (G : Type _) where op : G → G → G
infixl:65 " ◇ " => Magma.op


-- Problem normal_0355: eq899 → eq4591

theorem problem_normal_0492 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G), x = y ◇ (x ◇ ((z ◇ y) ◇ y)))
    : ∀ (x : G) (y : G), x = ((x ◇ x) ◇ x) ◇ (y ◇ y) := by
  intro x y;
  convert h x _ _ using 1;
  rotate_left;
  exact x;
  exact y;
  grind

-- Problem normal_0500: eq2215 → eq3622
