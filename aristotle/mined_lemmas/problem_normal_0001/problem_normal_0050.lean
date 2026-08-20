

class Magma (G : Type _) where op : G → G → G
infixl:65 " ◇ " => Magma.op

/-
Problem normal_0001: eq2918 → eq1911
-/

theorem problem_normal_0050 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G), x = (y ◇ x) ◇ (y ◇ (z ◇ y)))
    : ∀ (x : G) (y : G) (z : G) (w : G), x = ((y ◇ z) ◇ w) ◇ (y ◇ w) := by
  revert ‹_›;
  intro h y;
  have := h y;
  have h_eq : ∀ y_1 z, (‹Magma G›.op y_1 y) = (‹Magma G›.op y_1 (‹Magma G›.op z y_1)) := by
    grind;
  grind

/-
Problem normal_0060: eq1367 → eq341
-/
