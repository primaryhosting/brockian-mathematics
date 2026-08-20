import Mathlib.Tactic

set_option quotPrecheck false
class Magma (G : Type _) where op : G → G → G
infixl:65 " ◇ " => Magma.op


-- Problem normal_0355: eq899 → eq4591

theorem problem_normal_0384 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G) (w : G), x = y ◇ (x ◇ (z ◇ (w ◇ w))))
    : ∀ (x : G) (y : G), x = (y ◇ ((x ◇ x) ◇ y)) ◇ y := by
  -- Let's denote the magma operation by `op`.
  set op := (‹Magma G›.op);
  -- Let's choose any two elements $x$ and $y$ in the magma $G$.
  intro x y
  -- By the given equation, we have $x = y ◇ (x ◇ (z ◇ (w ◇ w)))$ for all $z$ and $w$.
  have h_eq : ∀ z w, x = op y (op x (op z (op w w))) := by
    exact fun z w => h x y z w;
  convert h_eq _ _ using 1;
  rotate_left;
  exact op y y;
  exact (op (op x x) x ◇ op (op x x) x);
  grind

-- Problem normal_0385: eq1509 → eq983
