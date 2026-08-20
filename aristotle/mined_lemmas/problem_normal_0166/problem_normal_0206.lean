import Mathlib.Tactic

class Magma (G : Type _) where op : G → G → G
set_option quotPrecheck false in
infixl:65 " ◇ " => Magma.op


-- Problem normal_0166: eq1359 → eq210

theorem problem_normal_0206 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x ◇ y = z ◇ ((z ◇ w) ◇ u))
    : ∀ (x : G) (y : G) (z : G), x ◇ (y ◇ y) = (x ◇ z) ◇ x := by
  grind

-- Problem normal_0212: eq3391 → eq4539
