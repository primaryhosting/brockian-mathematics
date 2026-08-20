import Mathlib.Tactic

class Magma (G : Type _) where op : G → G → G
set_option quotPrecheck false in
infixl:65 " ◇ " => Magma.op


-- Problem normal_0166: eq1359 → eq210

theorem problem_normal_0324 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G), x ◇ x = ((y ◇ x) ◇ x) ◇ z)
    : ∀ (x : G) (y : G) (z : G), x ◇ x = ((y ◇ z) ◇ z) ◇ x := by
  intro x y z;
  -- We consider the two cases: $x = y$ and $x \neq y$.
  by_contra hxy; have := h x x z; have := h y x z; have := h x z x; have := h y z x; have := h x x y; have := h y x y; have := h x z y; have := h y z y;
  grind +ring

-- Problem normal_0325: eq3618 → eq312
