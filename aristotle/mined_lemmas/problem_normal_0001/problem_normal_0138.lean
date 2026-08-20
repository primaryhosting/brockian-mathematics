

class Magma (G : Type _) where op : G → G → G
infixl:65 " ◇ " => Magma.op

/-
Problem normal_0001: eq2918 → eq1911
-/

theorem problem_normal_0138 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G), x = y ◇ ((x ◇ x) ◇ z))
    : ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x ◇ (y ◇ z) = (w ◇ w) ◇ u := by
  -- By the properties of the magma, if x = y ◇ x, then x is idempotent. Therefore, we can rewrite x ◇ (y ◇ z) as c ◇ (c ◇ z) for some constant c.
  have h_idempotent : ∀ x y : G, x = y := by
    intro x y;
    rw [ h x y y, h y x x ];
    rw [ ← h ];
    convert h x _ _ using 1;
    congr! 1;
    convert h _ _ _ using 1;
    exact x;
  grind

/-
Problem normal_0140: eq2399 → eq1832
-/
