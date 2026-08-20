import Mathlib.Tactic

class Magma (G : Type _) where op : G → G → G
set_option quotPrecheck false in
infixl:65 " ◇ " => Magma.op


-- Problem normal_0166: eq1359 → eq210

theorem problem_normal_0282 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G) (w : G), x = x ◇ (((y ◇ z) ◇ z) ◇ w))
    : ∀ (x : G) (y : G) (z : G), x ◇ x = (x ◇ (y ◇ z)) ◇ z := by
  intro x y z
  have := h x y z x
  have := h x y z z
  have := h x z y z
  have := h x z z y
  have := h x x x x
  have := h (x ◇ x) y z x
  have := h y x z x; have := h y x x z; have := h y y x z; have := h y y y x; have := h y y z x; have := h y y z y; have := h y y y y; have := h y y y z; have := h y y z z; have := h y y z y; have := h y y y y; have := h y y y z; have := h y y z z;
  grind +ring

/-
Problem normal_0285: eq1909 → eq4003
-/
