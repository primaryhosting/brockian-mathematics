import Mathlib.Tactic

set_option quotPrecheck false
class Magma (G : Type _) where op : G → G → G
infixl:65 " ◇ " => Magma.op


-- Problem normal_0355: eq899 → eq4591

theorem problem_normal_0412 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G), x ◇ y = ((y ◇ x) ◇ z) ◇ x)
    : ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = z ◇ ((x ◇ w) ◇ y) := by
  intro x y z;
  -- Let's choose any $w$ and derive the expression $x ◇ y = z ◇ (x ◇ w ◇ y)$.
  intro w;
  convert h y _ _ using 1;
  rotate_left 1;
  convert h _ _ _ using 1;
  rotate_left;
  exact y;
  exact ( ‹Magma G›.op ( ‹Magma G›.op x w ) y );
  exact z;
  · convert h x y ( ‹Magma G›.op x w ) using 1;
    grind;
  · grind

/-
Problem normal_0414: eq1433 → eq1859
-/
