import Mathlib.Tactic

class Magma (G : Type _) where op : G → G → G
set_option quotPrecheck false in
infixl:65 " ◇ " => Magma.op


-- Problem normal_0166: eq1359 → eq210

theorem problem_normal_0243 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G), x = ((y ◇ z) ◇ x) ◇ (z ◇ z))
    : ∀ (x : G) (y : G) (z : G), x ◇ y = (z ◇ (y ◇ x)) ◇ x := by
  intro x y z
  have h1 := h x x x; have h2 := h x y z; have h3 := h y z x; have h4 := h z x y
  have h5 := h z y z; have h6 := h x x y; have h7 := h x y x; have h8 := h y x z
  grind +ring

/-
Problem normal_0250: eq2529 → eq1292
-/
