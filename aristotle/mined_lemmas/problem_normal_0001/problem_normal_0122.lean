

class Magma (G : Type _) where op : G → G → G
infixl:65 " ◇ " => Magma.op

/-
Problem normal_0001: eq2918 → eq1911
-/

theorem problem_normal_0122 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G), x = y ◇ (y ◇ (x ◇ z)))
    : ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x = (y ◇ ((z ◇ x) ◇ w)) ◇ u := by
  intros x y z w u049;
  -- From the given identity, we have $x = y \circ (y \circ (x \circ z))$.
  have h1 : ∀ x y z, (x = (‹Magma G›.op y (‹Magma G›.op y (‹Magma G›.op x z)))) := by
    exact h;
  -- By applying the given identity three times, we can transform the goal into the form of the given identity.
  have := h1 x y z
  have := h1 (‹Magma G›.op y (‹Magma G›.op z x)) w u049
  have := h1 (‹Magma G›.op y (‹Magma G›.op (‹Magma G›.op z x) w)) u049 (‹Magma G›.op y (‹Magma G›.op z x));
  grind

/-
Problem normal_0124: eq1725 → eq2635
-/
