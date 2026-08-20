import Mathlib.Tactic

class Magma (G : Type _) where op : G → G → G
set_option quotPrecheck false in
infixl:65 " ◇ " => Magma.op


-- Problem normal_0166: eq1359 → eq210

theorem problem_normal_0270 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G) (w : G), x = ((y ◇ (z ◇ w)) ◇ x) ◇ z)
    : ∀ (x : G) (y : G), x = (y ◇ y) ◇ y := by
  intro x y;
  have h1 := h x y y y;
  grind +ring

-- Problem normal_0278: eq3125 → eq583
