import Mathlib.Tactic

set_option quotPrecheck false
class Magma (G : Type _) where op : G → G → G
infixl:65 " ◇ " => Magma.op


-- Problem normal_0355: eq899 → eq4591

theorem problem_normal_0404 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G), x = (y ◇ x) ◇ (z ◇ (x ◇ y)))
    : ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x = (((y ◇ z) ◇ w) ◇ u) ◇ w := by
  -- From the hypothesis h, let's derive that all elements in G are equal to a single constant value. First, notice the structure here.
  have hall : ∀ x y : G, x = y := by
    intro x y
    have hx := h x y y
    have hy := h y x x
    grind;
  exact fun x y z w u => hall _ _

/-
Problem normal_0412: eq4160 → eq3595
-/
