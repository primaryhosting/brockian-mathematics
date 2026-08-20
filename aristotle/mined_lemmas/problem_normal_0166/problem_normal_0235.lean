import Mathlib.Tactic

class Magma (G : Type _) where op : G → G → G
set_option quotPrecheck false in
infixl:65 " ◇ " => Magma.op


-- Problem normal_0166: eq1359 → eq210

theorem problem_normal_0235 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G), x = (y ◇ z) ◇ (x ◇ (x ◇ z)))
    : ∀ (x : G) (y : G), x = x ◇ (x ◇ (x ◇ (y ◇ x))) := by
  intro x
  have h2 := h x x
  grind

-- Problem normal_0243: eq2171 → eq4005
