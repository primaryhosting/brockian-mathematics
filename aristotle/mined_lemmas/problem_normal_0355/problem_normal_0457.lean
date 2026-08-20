import Mathlib.Tactic

set_option quotPrecheck false
class Magma (G : Type _) where op : G → G → G
infixl:65 " ◇ " => Magma.op


-- Problem normal_0355: eq899 → eq4591

theorem problem_normal_0457 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G) (w : G), x = (((y ◇ z) ◇ y) ◇ w) ◇ x)
    : ∀ (x : G) (y : G) (z : G), x = y ◇ (z ◇ (z ◇ (x ◇ x))) := by
  have h_eq : ∀ t x : G, x = (‹Magma G›).op (‹Magma G›.op (‹Magma G›.op (‹Magma G›.op t x) t) x) x := by
    exact fun t x => h x t x x;
  grind

-- Problem normal_0460: eq3126 → eq3962
