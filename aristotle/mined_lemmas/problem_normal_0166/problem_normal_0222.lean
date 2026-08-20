import Mathlib.Tactic

class Magma (G : Type _) where op : G → G → G
set_option quotPrecheck false in
infixl:65 " ◇ " => Magma.op


-- Problem normal_0166: eq1359 → eq210

theorem problem_normal_0222 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G) (w : G), x = y ◇ ((x ◇ (z ◇ w)) ◇ w))
    : ∀ (x : G) (y : G) (z : G) (w : G), x = (y ◇ (z ◇ w)) ◇ (y ◇ z) := by
  have h_all_eq : ∀ (x y : G), x = y := by
    intro x y
    have h1 := h x y x x
    have h2 := h y x x x
    have h3 := h x x y y
    have h4 := h y y x x
    grind
  exact fun x y z w => h_all_eq _ _

-- Problem normal_0225: eq3444 → eq4001
