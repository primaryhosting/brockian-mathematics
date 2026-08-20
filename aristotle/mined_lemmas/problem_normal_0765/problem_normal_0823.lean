
import Mathlib.Tactic

set_option quotPrecheck false
class Magma (G : Type _) where op : G → G → G
infixl:65 " ◇ " => Magma.op

/-
Problem normal_0765: eq1708 → eq3230
-/

theorem problem_normal_0823 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x = (y ◇ (z ◇ (x ◇ w))) ◇ u)
    : ∀ (x : G) (y : G) (z : G) (w : G), x ◇ (x ◇ y) = (z ◇ y) ◇ w := by
  have := h;
  convert this using 1;
  constructor <;> intro h <;> have := h <;> simp +decide [ ← this ] at *;
  · exact?;
  · rename_i h₁ h₂;
    have := h₁ h₂ h₂ h₂ h₂ h₂;
    grind +suggestions

/-
Problem normal_0825: eq239 → eq1262
-/
