import Mathlib.Tactic

set_option quotPrecheck false
class Magma (G : Type _) where op : G → G → G
infixl:65 " ◇ " => Magma.op


-- Problem normal_0355: eq899 → eq4591

theorem problem_normal_0433 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = ((z ◇ y) ◇ z) ◇ w)
    : ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = (y ◇ z) ◇ (x ◇ w) := by
  -- Apply the given hypothesis `h` to rewrite `x ◇ y` in terms of `z` and `w`.
  intro x y z w
  rw [h x y z w];
  rw [ ← h, ← h ];
  exact x

/-
Problem normal_0445: eq2587 → eq1135
-/
