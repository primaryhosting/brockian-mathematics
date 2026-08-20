import Mathlib.Tactic

set_option quotPrecheck false
class Magma (G : Type _) where op : G → G → G
infixl:65 " ◇ " => Magma.op


-- Problem normal_0355: eq899 → eq4591

theorem problem_normal_0507 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = ((z ◇ y) ◇ x) ◇ w)
    : ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = ((z ◇ w) ◇ x) ◇ x := by
  -- Let's choose any two elements $x$ and $y$ from $G$.
  intro x y;
  convert h x y x x;
  constructor <;> intro h';
  · exact h' x y;
  · intro z w;
    convert h x y z w using 1;
    grind

-- Problem normal_0522: eq1531 → eq388
