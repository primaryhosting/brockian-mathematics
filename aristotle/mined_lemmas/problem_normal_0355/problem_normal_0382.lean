import Mathlib.Tactic

set_option quotPrecheck false
class Magma (G : Type _) where op : G → G → G
infixl:65 " ◇ " => Magma.op


-- Problem normal_0355: eq899 → eq4591

theorem problem_normal_0382 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G) (w : G), x = (y ◇ z) ◇ (w ◇ (x ◇ z)))
    : ∀ (x : G) (y : G) (z : G), x = (y ◇ (x ◇ y)) ◇ (x ◇ z) := by
  intro x y z
  have := h y z z z; have := h z z z z; have := h x z z z
  have := h x z y z; have := h y z x z; have := h z z x z
  grind

/-
Problem normal_0384: eq498 → eq2497
-/
