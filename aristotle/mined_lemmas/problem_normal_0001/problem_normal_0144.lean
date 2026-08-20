

class Magma (G : Type _) where op : G → G → G
infixl:65 " ◇ " => Magma.op

/-
Problem normal_0001: eq2918 → eq1911
-/

theorem problem_normal_0144 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G), x = (y ◇ (x ◇ y)) ◇ (z ◇ x))
    : ∀ (x : G) (y : G) (z : G), x = (y ◇ (z ◇ x)) ◇ (z ◇ x) := by
  -- From Lemma 2, we know that $a ◇ (b ◇ c) = c$ for all $a, b, c \in G$.
  have lemma2 : ∀ (a b c : G), (‹Magma G›.op a (‹Magma G›.op b c)) = c := by
    grind;
  grind

/-
Problem normal_0152: eq685 → eq1809
-/
