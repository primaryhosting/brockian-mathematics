

class Magma (G : Type _) where op : G → G → G
infixl:65 " ◇ " => Magma.op

/-
Problem normal_0001: eq2918 → eq1911
-/

theorem problem_normal_0042 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G) (w : G), x = (y ◇ (z ◇ x)) ◇ (w ◇ y))
    : ∀ (x : G) (y : G) (z : G) (w : G), x ◇ x = y ◇ (z ◇ (w ◇ y)) := by
  intro x y z w;
  have h1 := h x x x x;
  have h2 := h ( ‹Magma G›.op x x ) y z w;
  have h3 := h ( ‹Magma G›.op x x ) x x x;
  grind

/-
Problem normal_0046: eq1908 → eq1734
-/
