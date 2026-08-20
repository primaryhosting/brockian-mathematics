

class Magma (G : Type _) where op : G → G → G
infixl:65 " ◇ " => Magma.op

/-
Problem normal_0001: eq2918 → eq1911
-/

theorem problem_normal_0018 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G), x = y ◇ ((x ◇ (x ◇ y)) ◇ z))
    : ∀ (x : G) (y : G) (z : G) (w : G), x = y ◇ (z ◇ ((x ◇ y) ◇ w)) := by
  -- Let's choose anyarbitrary $x, y, z, w \in G$.
  intro x y z w;
  convert h x z _ using 1;
  rw [ ← h ];
  · convert h _ _ _ using 1;
    convert h x y w using 1;
    congr! 1;
    convert h _ _ _ using 1;
    congr! 1;
    convert h _ _ _ using 1;
    · exact x;
    · exact x;
  · exact x

/-
Problem normal_0022: eq2738 → eq3451
-/
