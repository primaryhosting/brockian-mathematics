import Mathlib.Tactic

class Magma (G : Type _) where op : G → G → G
set_option quotPrecheck false in
infixl:65 " ◇ " => Magma.op


-- Problem normal_0166: eq1359 → eq210

theorem problem_normal_0330 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G), x = (((y ◇ x) ◇ y) ◇ x) ◇ z)
    : ∀ (x : G) (y : G) (z : G) (w : G), x = (y ◇ z) ◇ ((z ◇ w) ◇ w) := by
  intro x y z w
  have h_eq : ∀ x y : G, x = y := by
    intro x y
    have h1 : ∀ x y : G, x = (‹Magma G›.op (‹Magma G›.op (‹Magma G›.op (‹Magma G›.op y x) y) x) y) := by
      exact fun x y => h x y y
    have := h1 x y
    grind
  exact h_eq _ _

/-
Problem normal_0331: eq2524 → eq1988
-/
