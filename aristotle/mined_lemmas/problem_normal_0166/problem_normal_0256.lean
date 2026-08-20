import Mathlib.Tactic

class Magma (G : Type _) where op : G → G → G
set_option quotPrecheck false in
infixl:65 " ◇ " => Magma.op


-- Problem normal_0166: eq1359 → eq210

theorem problem_normal_0256 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G), x = y ◇ (y ◇ (z ◇ (x ◇ y))))
    : ∀ (x : G) (y : G), x = (y ◇ y) ◇ (x ◇ (x ◇ x)) := by
  intro x y
  have h1 := h x x x
  have h2 := h x y x
  have h3 := h y x y
  have h4 := h x x y
  have h5 := h y y x
  grind

/-
Problem normal_0257: eq573 → eq719
-/
