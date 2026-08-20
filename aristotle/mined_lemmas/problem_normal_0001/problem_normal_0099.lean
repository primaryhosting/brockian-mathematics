

class Magma (G : Type _) where op : G → G → G
infixl:65 " ◇ " => Magma.op

/-
Problem normal_0001: eq2918 → eq1911
-/

theorem problem_normal_0099 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G) (w : G), x = y ◇ ((x ◇ x) ◇ (z ◇ w)))
    : ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x ◇ y = (y ◇ z) ◇ (w ◇ u) := by
  intro x y z u;
  intro wm;
  convert h _ _ _ _;
  all_goals congr! 1;
  · convert h u _ _ _;
    convert h x _ _ _;
    convert h u _ _ _;
    exact u;
    exact ( ‹Magma G›.op ( ‹Magma G›.op y y ) ( ‹Magma G›.op u wm ) );
    convert h y _ _ _;
    · exact x;
    · exact x;
    · exact x;
  · convert h _ _ _ _;
    convert h _ _ _ _;
    · exact x;
    · exact x

/-
Problem normal_0101: eq4215 → eq386
-/
