
import Mathlib.Tactic

set_option quotPrecheck false
class Magma (G : Type _) where op : G → G → G
infixl:65 " ◇ " => Magma.op

/-
Problem normal_0765: eq1708 → eq3230
-/

theorem problem_normal_0927 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G), x = (y ◇ x) ◇ ((x ◇ x) ◇ z))
    : ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = x ◇ ((z ◇ x) ◇ w) := by
  intro x y z w;
  have := h x x x; have := h x ( ‹Magma G›.op x x ) x; have := h x x ( ‹Magma G›.op x x ) ; have := h ( ‹Magma G›.op x x ) x x; have := h ( ‹Magma G›.op x x ) ( ‹Magma G›.op x x ) x; have := h ( ‹Magma G›.op x x ) x ( ‹Magma G›.op x x ) ; norm_num at * ;
  have h_eq : ∀ y : G, ‹Magma G›.op x y = x := by
    intro y; have := h x y x; have := h x ( ‹Magma G›.op x y ) x; have := h ( ‹Magma G›.op x y ) x x; have := h ( ‹Magma G›.op x y ) ( ‹Magma G›.op x y ) x; have := h ( ‹Magma G›.op x y ) x ( ‹Magma G›.op x y ) ; norm_num at * ;
    grind +ring;
  exact (Eq.to_iff (congrArg (Eq (x ◇ y)) (h_eq (z ◇ x ◇ w)))).mpr (h_eq y)

/-
Problem normal_0932: eq116 → eq3189
-/
