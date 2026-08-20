import Mathlib.Tactic

set_option quotPrecheck false
class Magma (G : Type _) where op : G → G → G
infixl:65 " ◇ " => Magma.op


-- Problem normal_0355: eq899 → eq4591

theorem problem_normal_0392 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G), x = y ◇ ((z ◇ (z ◇ x)) ◇ z))
    : ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x ◇ (x ◇ y) = (z ◇ w) ◇ u := by
  -- This implies all elements of G are equal.
  have h_eq (x y : G) : x = y := by
    convert h x _ _ using 1;
    convert h y _ _ using 1;
    congr! 1;
    convert h _ _ _ using 1;
    · exact x;
    · exact x;
    · exact x;
  exact fun x y z w u => h_eq _ _

-- Problem normal_0394: eq494 → eq4055
