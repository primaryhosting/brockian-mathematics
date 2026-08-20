import Mathlib.Tactic

set_option quotPrecheck false
class Magma (G : Type _) where op : G → G → G
infixl:65 " ◇ " => Magma.op


-- Problem normal_0355: eq899 → eq4591

theorem problem_normal_0483 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G), x = (y ◇ y) ◇ (y ◇ (x ◇ z)))
    : ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = z ◇ (w ◇ z) := by
  intro x y z w; have h1 := h x y; grind

/-
Problem normal_0484: eq2788 → eq3030
-/
