import Mathlib.Tactic

set_option quotPrecheck false
class Magma (G : Type _) where op : G → G → G
infixl:65 " ◇ " => Magma.op


-- Problem normal_0355: eq899 → eq4591

theorem problem_normal_0449 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G) (w : G), x = y ◇ ((x ◇ z) ◇ (z ◇ w)))
    : ∀ (x : G) (y : G) (z : G), x = ((y ◇ (y ◇ z)) ◇ y) ◇ z := by
  intro x y z;
  convert h x _ _ _;
  convert h z _ _ _;
  · exact x;
  · exact x

/-
Problem normal_0457: eq3205 → eq571
-/
