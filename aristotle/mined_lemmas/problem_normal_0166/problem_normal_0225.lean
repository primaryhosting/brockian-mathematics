import Mathlib.Tactic

class Magma (G : Type _) where op : G → G → G
set_option quotPrecheck false in
infixl:65 " ◇ " => Magma.op


-- Problem normal_0166: eq1359 → eq210

theorem problem_normal_0225 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x ◇ y = z ◇ (w ◇ (z ◇ u)))
    : ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = (z ◇ (x ◇ w)) ◇ y := by
  grind +splitImp

-- Problem normal_0227: eq2377 → eq1139
