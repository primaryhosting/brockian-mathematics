import Mathlib.Tactic

class Magma (G : Type _) where op : G → G → G
set_option quotPrecheck false in
infixl:65 " ◇ " => Magma.op


-- Problem normal_0166: eq1359 → eq210

theorem problem_normal_0257 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G), x = y ◇ (z ◇ (z ◇ (x ◇ z))))
    : ∀ (x : G) (y : G) (z : G), x = y ◇ (y ◇ ((y ◇ z) ◇ x)) := by
  -- Apply the hypothesis `h` with `x` and `y` swapped.
  have h_swap := fun x y z => h x y z;
  have h_swap := fun x y => h_swap x x y;
  grind

/-
Problem normal_0260: eq1808 → eq3695
-/
