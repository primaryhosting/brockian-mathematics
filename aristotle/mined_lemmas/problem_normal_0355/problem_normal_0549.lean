import Mathlib.Tactic

set_option quotPrecheck false
class Magma (G : Type _) where op : G → G → G
infixl:65 " ◇ " => Magma.op


-- Problem normal_0355: eq899 → eq4591

theorem problem_normal_0549 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G), x = (y ◇ ((x ◇ z) ◇ z)) ◇ x)
    : ∀ (x : G) (y : G) (z : G) (w : G), x = (((y ◇ z) ◇ w) ◇ y) ◇ x := by
  -- First line of provided solution
  intro x y z w;
  have := h x y z;
  convert h x _ _ using 1;
  congr! 2;
  convert h _ _ _;
  swap;
  exact ( ‹Magma G›.op ( ‹Magma G›.op y ( ‹Magma G›.op ( ‹Magma G›.op y w ) w ) ) y );
  convert h _ _ _ using 1;
  grind;
  · exact x;
  · exact x

-- Problem normal_0551: eq15 → eq1527
