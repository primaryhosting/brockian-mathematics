import Mathlib.Tactic

class Magma (G : Type _) where op : G → G → G
set_option quotPrecheck false in
infixl:65 " ◇ " => Magma.op


-- Problem normal_0166: eq1359 → eq210

theorem problem_normal_0329 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G) (w : G), x = (y ◇ z) ◇ (w ◇ (x ◇ z)))
    : ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x = (y ◇ ((z ◇ w) ◇ y)) ◇ u := by
  -- All elements equal.
  have h_all_eq : ∀ x y : G, x = y := by
    intros x y
    have h1 := h x x x x
    have h2 := h y y y y
    have h3 := h x y x y
    have h4 := h y x y x
    grind +ring;
  exact fun x y z w u => h_all_eq _ _

-- Problem normal_0330: eq3114 → eq1804
