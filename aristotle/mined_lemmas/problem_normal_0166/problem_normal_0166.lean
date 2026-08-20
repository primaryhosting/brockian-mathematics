import Mathlib.Tactic

class Magma (G : Type _) where op : G → G → G
set_option quotPrecheck false in
infixl:65 " ◇ " => Magma.op


-- Problem normal_0166: eq1359 → eq210

theorem problem_normal_0166 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G), x = y ◇ (((z ◇ x) ◇ z) ◇ z))
    : ∀ (x : G) (y : G) (z : G), x = (x ◇ (y ◇ x)) ◇ z := by
  have h2 : ∀ x z : G, x = (‹Magma G›.op x (‹Magma G›.op (‹Magma G›.op (‹Magma G›.op z x) z) z)) := by
    exact fun x z => h x x z
  grind +splitIndPred

-- Problem normal_0169: eq2781 → eq2758
