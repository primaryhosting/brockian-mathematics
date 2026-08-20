

class Magma (G : Type _) where op : G → G → G
infixl:65 " ◇ " => Magma.op

/-
Problem normal_0001: eq2918 → eq1911
-/

theorem problem_normal_0023 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G), x = (y ◇ (x ◇ (z ◇ x))) ◇ y)
    : ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = x ◇ ((z ◇ w) ◇ z) := by
  revert @‹Magma G›; (
  intro inst h x y z w;
  -- By the given hypothesis, we can rewrite the goal using the equality $x = (y ◇ (x ◇ (z ◇ x))) ◇ y$.
  have h_eq : ∀ x y z : G, x = inst.op (inst.op y (inst.op x (inst.op z x))) y := by
    exact h;
  -- By the given hypothesis, we can rewrite the goal using the equality $x = (y ◇ (x ◇ (z ◇ x))) ◇ y$ for any $x, y, z$.
  have h_eq : ∀ x y : G, x = inst.op (inst.op y (inst.op x (inst.op y x))) y := by
    exact fun x y => h_eq x y y;
  grind +ring)

/-
Problem normal_0032: eq3368 → eq3563
-/
