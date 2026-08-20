import Mathlib.Tactic

set_option quotPrecheck false
class Magma (G : Type _) where op : G → G → G
infixl:65 " ◇ " => Magma.op


-- Problem normal_0355: eq899 → eq4591

theorem problem_normal_0475 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G) (w : G), x = (y ◇ x) ◇ (z ◇ (w ◇ y)))
    : ∀ (x : G) (y : G) (z : G), x = x ◇ (y ◇ (x ◇ (z ◇ y))) := by
  intro x y z;
  convert h x _ _ _;
  convert h x _ _ _;
  rotate_left;
  convert h x _ _ _;
  convert h z _ _ _;
  · exact x;
  · exact x;
  · exact x;
  · exact x;
  · convert h y _ _ _;
    rotate_left;
    exact y;
    exact z;
    exact y;
    convert h x y y y using 1;
    grind

-- Problem normal_0476: eq1739 → eq3888
