import Mathlib.Tactic

set_option quotPrecheck false
class Magma (G : Type _) where op : G → G → G
infixl:65 " ◇ " => Magma.op


-- Problem normal_0355: eq899 → eq4591

theorem problem_normal_0578 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x ◇ y = z ◇ (x ◇ (w ◇ u)))
    : ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = (x ◇ z) ◇ (w ◇ z) := by
  intro x y z;
  convert h x y ( ‹Magma G›.op x z ) z z using 1;
  grind
