import Mathlib.Tactic

set_option quotPrecheck false
class Magma (G : Type _) where op : G → G → G
infixl:65 " ◇ " => Magma.op


-- Problem normal_0355: eq899 → eq4591

theorem problem_normal_0548 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G) (w : G), x = ((y ◇ z) ◇ z) ◇ (x ◇ w))
    : ∀ (x : G) (y : G), x = y ◇ ((x ◇ y) ◇ (y ◇ x)) := by
  -- Let's choose any two elements $x$ and $y$ in $G$.
  intro x y;
  convert h x _ _ _;
  convert h y _ _ _;
  · exact x;
  · exact x;
  · convert h ( _ ) _ _ _;
    rotate_left;
    exact y;
    exact y;
    exact y;
    grind +suggestions

/-
Problem normal_0549: eq2521 → eq3232
-/
