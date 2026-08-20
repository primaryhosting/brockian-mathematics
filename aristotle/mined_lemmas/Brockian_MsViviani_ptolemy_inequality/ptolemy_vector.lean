import Mathlib
namespace Brockian.MsViviani

/-- The inversion map `x ↦ ‖x‖⁻² • x` scales distances by `(‖x‖ * ‖y‖)⁻¹`. -/

private lemma ptolemy_vector {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (a b c : E) :
    ‖a - c‖ * ‖b‖ ≤ ‖a - b‖ * ‖c‖ + ‖b - c‖ * ‖a‖ := by
  rcases eq_or_ne a 0 with rfl | ha
  · simp [mul_comm]
  rcases eq_or_ne b 0 with rfl | hb
  · simp; positivity
  rcases eq_or_ne c 0 with rfl | hc
  · simp [mul_comm]
  exact ptolemy_vector_ne_zero a b c ha hb hc

/-- Ptolemy's inequality: for any four points in an inner product space,
    dist A C · dist B D ≤ dist A B · dist C D + dist B C · dist A D. -/
