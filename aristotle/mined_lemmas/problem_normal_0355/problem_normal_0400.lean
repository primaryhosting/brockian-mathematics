import Mathlib.Tactic

set_option quotPrecheck false
class Magma (G : Type _) where op : G → G → G
infixl:65 " ◇ " => Magma.op


-- Problem normal_0355: eq899 → eq4591

theorem problem_normal_0400 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G) (w : G), x = y ◇ (z ◇ (w ◇ (x ◇ w))))
    : ∀ (x : G) (y : G), x ◇ (x ◇ y) = (x ◇ y) ◇ x := by
  intro x y;
  -- Let's use the given identity to express $x$ in terms of other elements.
  have hx : ∀ x y z w : G, x = (‹Magma G›.op y) ((‹Magma G›.op z) ((‹Magma G›.op w) ((‹Magma G›.op x) w))) := by
    exact h;
  convert hx _ _ _ _;
  convert hx _ _ _ _;
  exact x

-- Problem normal_0401: eq2516 → eq3360
