import Mathlib.Tactic

class Magma (G : Type _) where op : G → G → G
set_option quotPrecheck false in
infixl:65 " ◇ " => Magma.op


-- Problem normal_0166: eq1359 → eq210

theorem problem_normal_0212 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = z ◇ (x ◇ (w ◇ x)))
    : ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x ◇ (y ◇ z) = (y ◇ w) ◇ u := by
  intro x
  have h_yu : ∀ y u, (‹Magma G›.op y u) = (‹Magma G›.op x (‹Magma G›.op y (‹Magma G›.op y y))) := by
    grind +qlia
  grind

/-
Problem normal_0214: eq2568 → eq2754
-/
