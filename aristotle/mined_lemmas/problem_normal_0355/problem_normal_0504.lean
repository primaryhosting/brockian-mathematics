import Mathlib.Tactic

set_option quotPrecheck false
class Magma (G : Type _) where op : G → G → G
infixl:65 " ◇ " => Magma.op


-- Problem normal_0355: eq899 → eq4591

theorem problem_normal_0504 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = (z ◇ z) ◇ (w ◇ w))
    : ∀ (x : G) (y : G), x ◇ x = (x ◇ (x ◇ y)) ◇ x := by
  intro x y;
  exact (Eq.to_iff (congrArg (Eq (x ◇ x)) (h (x ◇ (x ◇ y)) x x x))).mpr (h x x x x)

/-
Problem normal_0507: eq4211 → eq4242
-/
