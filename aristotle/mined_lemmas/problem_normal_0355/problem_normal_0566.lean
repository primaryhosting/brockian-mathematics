import Mathlib.Tactic

set_option quotPrecheck false
class Magma (G : Type _) where op : G → G → G
infixl:65 " ◇ " => Magma.op


-- Problem normal_0355: eq899 → eq4591

theorem problem_normal_0566 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x ◇ y = z ◇ (w ◇ (u ◇ x)))
    : ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = z ◇ (y ◇ (y ◇ w)) := by
  have := h;
  convert this using 1;
  constructor <;> intro h;
  · grind;
  · rename_i a ha;
    have := h ha; have := h ha ( ‹Magma G›.op ha ha ) ; have := h ( ‹Magma G›.op ha ha ) ha; have := h ( ‹Magma G›.op ha ha ) ( ‹Magma G›.op ha ha ) ; simp_all +decide [ ← this ] ;
    grind

-- Problem normal_0567: eq756 → eq213
