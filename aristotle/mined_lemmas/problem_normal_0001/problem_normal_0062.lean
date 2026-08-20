

class Magma (G : Type _) where op : G → G → G
infixl:65 " ◇ " => Magma.op

/-
Problem normal_0001: eq2918 → eq1911
-/

theorem problem_normal_0062 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G), x = ((y ◇ x) ◇ (y ◇ z)) ◇ y)
    : ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x = ((y ◇ z) ◇ (y ◇ w)) ◇ u := by
  intro x y z u;
  intros w
  have h_yx : ∀ y z, (‹Magma G›.op y z) = y := by
    intro y z
    have := h (‹Magma G›.op y z) y z
    have := h y y z
    have := h (‹Magma G›.op y z) (‹Magma G›.op y z) z
    have := h y (‹Magma G›.op y z) z
    have := h (‹Magma G›.op y z) y y
    have := h y y y
    have := h (‹Magma G›.op y z) (‹Magma G›.op y z) y
    have := h y (‹Magma G›.op y z) y
    grind +ring;
  aesop ( simp_config := { singlePass := true } )

/-
Problem normal_0063: eq2914 → eq2171
-/
