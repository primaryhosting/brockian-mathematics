import Mathlib
namespace Brockian.MsStewart

/-- Algebraic core of Stewart's theorem in an inner product space. -/

private lemma stewart_aux {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (u v : E) (t : ℝ) :
    ‖u‖ ^ 2 * (1 - t) + ‖u - v‖ ^ 2 * t = ‖u - t • v‖ ^ 2 + t * (1 - t) * ‖v‖ ^ 2 := by
  norm_num [norm_sub_sq_real, norm_smul, real_inner_smul_right]
  rw [mul_pow, sq_abs]
  ring

/-- Stewart's theorem: for a point D on segment BC of a triangle,
    |AB|²·|DC| + |AC|²·|BD| = |BC|·(|AD|² + |BD|·|DC|). -/
