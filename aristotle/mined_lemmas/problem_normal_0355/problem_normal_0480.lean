import Mathlib.Tactic

set_option quotPrecheck false
class Magma (G : Type _) where op : G → G → G
infixl:65 " ◇ " => Magma.op


-- Problem normal_0355: eq899 → eq4591

theorem problem_normal_0480 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G), x = y ◇ ((x ◇ y) ◇ (y ◇ z)))
    : ∀ (x : G) (y : G) (z : G), x ◇ x = (y ◇ z) ◇ (x ◇ y) := by
  have h_inv : ∀ x y : G, x = (‹Magma G›.op y (‹Magma G›.op (‹Magma G›.op x y) (‹Magma G›.op y y))) := by
    exact fun x y => h x y y;
  grind

-- Problem normal_0483: eq1527 → eq356
