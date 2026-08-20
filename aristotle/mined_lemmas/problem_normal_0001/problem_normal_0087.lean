

class Magma (G : Type _) where op : G → G → G
infixl:65 " ◇ " => Magma.op

/-
Problem normal_0001: eq2918 → eq1911
-/

theorem problem_normal_0087 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G), x = y ◇ ((x ◇ y) ◇ (z ◇ y)))
    : ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = (z ◇ (w ◇ w)) ◇ w := by
  intros x y z w;
  -- First, we show that $x = x ◇ (x ◇ x)$ for all $x$.
  have h1 : ∀ x : G, x = (‹Magma G›.op x (‹Magma G›.op x x)) := by
    intro x;
    convert h x x x using 1;
    convert h ( _ ) x x using 1;
    grind;
  convert h _ _ _ using 1;
  convert h _ _ _ using 1;
  rotate_left;
  exact ( ‹Magma G›.op ( ‹Magma G›.op z ( ‹Magma G›.op w w ) ) w );
  exact ( ‹Magma G›.op ( ‹Magma G›.op z ( ‹Magma G›.op w w ) ) w );
  exact ( ‹Magma G›.op ( ‹Magma G›.op z ( ‹Magma G›.op w w ) ) w );
  exact ( ‹Magma G›.op ( ‹Magma G›.op z ( ‹Magma G›.op w w ) ) w );
  grind

/-
Problem normal_0090: eq2398 → eq2456
-/
