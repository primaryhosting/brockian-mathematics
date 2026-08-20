import Mathlib.Tactic

class Magma (G : Type _) where op : G → G → G
set_option quotPrecheck false in
infixl:65 " ◇ " => Magma.op


-- Problem normal_0166: eq1359 → eq210

theorem problem_normal_0322 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G), x = y ◇ (z ◇ ((x ◇ y) ◇ y)))
    : ∀ (x : G) (y : G) (z : G) (w : G), x = y ◇ (((x ◇ x) ◇ z) ◇ w) := by
  have eq1 := h;
  -- The provided solution uses "grind", which in our custom Lean means doing many applications. We start by having the goal and, for completeness, introducing the variables.
  intro x y z w
  have h1 := eq1 x x x
  have h2 := eq1 x y z
  have h3 := eq1 x y w
  have h4 := eq1 x x y
  grind

/-
Problem normal_0324: eq4082 → eq4108
-/
