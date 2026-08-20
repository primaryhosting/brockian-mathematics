

class Magma (G : Type _) where op : G → G → G
infixl:65 " ◇ " => Magma.op

/-
Problem normal_0001: eq2918 → eq1911
-/

theorem problem_normal_0154 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G), x = ((y ◇ (y ◇ z)) ◇ x) ◇ y)
    : ∀ (x : G) (y : G) (z : G) (w : G), x = (y ◇ z) ◇ (w ◇ z) := by
  -- By applying the given condition h with x = y, we can derive that y = y ◇ (y ◇ z) ◇ y ◇ y.
  have h_idempotent : ∀ y z : G, y = (‹Magma G›.op y) (‹Magma G›.op (‹Magma G›.op y z) y) := by
    intros y z;
    have := h y y z;
    grind +splitImp;
  intro x y z w;
  convert h x ( ‹Magma G›.op y z ) ( ‹Magma G›.op w z ) using 1;
  grind

/-
Problem normal_0161: eq711 → eq3567
-/
