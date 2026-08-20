

class Magma (G : Type _) where op : G → G → G
infixl:65 " ◇ " => Magma.op

/-
Problem normal_0001: eq2918 → eq1911
-/

theorem problem_normal_0065 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G) (w : G), x = ((y ◇ z) ◇ w) ◇ (x ◇ y))
    : ∀ (x : G) (y : G) (z : G), x ◇ y = y ◇ (y ◇ (z ◇ z)) := by
  intro x y z;
  have := h x y y y; have := h x y z z; have := h y y z z; have := h y z z z; have := h z z z z; ( repeat' rw [ eq_comm ] at *; repeat' ( apply_rules [ h ] ) ; );
  -- Let's choose any $x, y \in G$ and derive a contradiction from the assumption that $x \neq y$.
  have h_eq : ∀ x y : G, x = y := by
    intro x y; exact (by
    have := h x x x x; have := h y x x x; have := h x y x x; have := h y y x x; have := h x x y x; have := h y x y x; have := h x y y x; have := h y y y x; have := h x x x y; have := h y x x y; have := h x y x y; have := h y y x y; have := h x x y y; have := h y x y y; have := h x y y y; have := h y y y y;
    grind +ring);
  grind

/-
Problem normal_0066: eq3831 → eq3869
-/
