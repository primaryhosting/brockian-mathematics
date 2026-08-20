import Mathlib.Tactic

class Magma (G : Type _) where op : G → G → G
set_option quotPrecheck false in
infixl:65 " ◇ " => Magma.op


-- Problem normal_0166: eq1359 → eq210

theorem problem_normal_0314 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G) (w : G), x = (y ◇ x) ◇ ((z ◇ w) ◇ w))
    : ∀ (x : G) (y : G) (z : G) (w : G), x ◇ (y ◇ y) = (z ◇ z) ◇ w := by
  intro a b c d;
  convert h _ _ _ _;
  rotate_left;
  rotate_left;
  exact d;
  exact ‹Magma G›.op d d;
  · convert h _ _ _ _;
    convert h _ _ _ _;
    rotate_left;
    exact b;
    exact (a ◇ a);
    exact c;
    rotate_left;
    exact ‹Magma G›.op ( ‹Magma G›.op b b ) b;
    · convert h _ _ _ _;
      rotate_left;
      exact c;
      exact c;
      convert h c c c c using 1;
      grind +suggestions;
    · convert h _ _ _ _;
      convert h _ _ _ _;
      rotate_left;
      exact b;
      exact b;
      exact b;
      convert h b b b b using 1;
      grind +suggestions;
  · grind +suggestions

/-
Problem normal_0317: eq2715 → eq1630
-/
