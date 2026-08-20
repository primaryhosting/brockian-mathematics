import Mathlib.Tactic

set_option quotPrecheck false
class Magma (G : Type _) where op : G → G → G
infixl:65 " ◇ " => Magma.op


-- Problem normal_0355: eq899 → eq4591

theorem problem_normal_0561 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G), x = y ◇ ((z ◇ (x ◇ x)) ◇ y))
    : ∀ (x : G) (y : G) (z : G), x = x ◇ (y ◇ ((y ◇ x) ◇ z)) := by
  revert h;
  intro h y z;
  intros w;
  convert h y _ _ using 1;
  convert h _ _ _ using 1;
  congr! 1;
  convert h _ _ _ using 1;
  congr! 1;
  convert h _ _ _ using 1;
  congr! 1;
  convert h _ _ _ using 1;
  · exact y;
  · exact y;
  · exact y

/-
Problem normal_0566: eq3450 → eq3403
-/
