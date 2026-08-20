
import Mathlib.Tactic

set_option quotPrecheck false
class Magma (G : Type _) where op : G → G → G
infixl:65 " ◇ " => Magma.op

/-
Problem normal_0765: eq1708 → eq3230
-/

theorem problem_normal_0793 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G) (w : G), x = y ◇ ((y ◇ (x ◇ z)) ◇ w))
    : ∀ (x : G) (y : G) (z : G), x ◇ x = y ◇ ((y ◇ y) ◇ z) := by
  -- Let's choose any $x, y, z \in G$.
  intro x y z
  have := h y z;
  convert h _ _ _ _;
  convert h _ _ _ _;
  · exact z;
  · exact x

/-
Problem normal_0798: eq1105 → eq940
-/
