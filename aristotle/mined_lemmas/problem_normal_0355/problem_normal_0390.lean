import Mathlib.Tactic

set_option quotPrecheck false
class Magma (G : Type _) where op : G → G → G
infixl:65 " ◇ " => Magma.op


-- Problem normal_0355: eq899 → eq4591

theorem problem_normal_0390 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G) (w : G), x = y ◇ (x ◇ ((z ◇ w) ◇ z)))
    : ∀ (x : G) (y : G), x = ((y ◇ x) ◇ y) ◇ x := by
  revert h;
  intro h y;
  intro z;
  convert h _ _ _ _ using 1;
  congr! 1;
  convert h _ _ _ _ using 1;
  congr! 1;
  convert h _ _ _ _ using 1;
  · exact y;
  · exact y

/-
Problem normal_0392: eq1182 → eq4431
-/
