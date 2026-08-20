import Mathlib.Tactic

set_option quotPrecheck false
class Magma (G : Type _) where op : G → G → G
infixl:65 " ◇ " => Magma.op


-- Problem normal_0355: eq899 → eq4591

theorem problem_normal_0465 (G : Type _) [Magma G]
    (h : ∀ (x : G) (y : G) (z : G) (w : G), x = y ◇ (z ◇ ((w ◇ x) ◇ w)))
    : ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x = (y ◇ z) ◇ (w ◇ (u ◇ w)) := by
  intro x y z w u; have := h x y z w; have := h y z w u; have := h z w u x; have := h w u x y; have := h u x y z; have := h x y z u; have := h y z u x; have := h z u x y; have := h u x y w;
  convert h x _ _ _;
  convert h u _ _ _;
  convert h x _ _ _;
  · exact x;
  · exact x

/-
Problem normal_0471: eq2215 → eq443
-/
