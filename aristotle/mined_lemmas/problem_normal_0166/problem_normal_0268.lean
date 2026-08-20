import Mathlib.Tactic

class Magma (G : Type _) where op : G → G → G
set_option quotPrecheck false in
infixl:65 " ◇ " => Magma.op


-- Problem normal_0166: eq1359 → eq210

theorem problem_normal_0268 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G), x = (y ◇ (x ◇ x)) ◇ z)
    : ∀ (x : G) (y : G) (z : G), x = y ◇ ((z ◇ (y ◇ y)) ◇ z) := by
  intro x y z;
  have h1 := h x y z;
  have h2 := h y x z;
  grind +suggestions

/-
Problem normal_0270: eq3026 → eq32
-/
