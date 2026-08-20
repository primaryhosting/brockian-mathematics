import Mathlib
namespace Brockian.MsViviani

/-- The inversion map `x ↦ ‖x‖⁻² • x` scales distances by `(‖x‖ * ‖y‖)⁻¹`. -/

theorem ptolemy_inequality {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (A B C D : E) :
    dist A C * dist B D ≤ dist A B * dist C D + dist B C * dist A D := by
  have h := ptolemy_vector (A - D) (B - D) (C - D)
  simpa [dist_eq_norm, sub_sub_sub_cancel_right] using h

end Brockian.MsViviani

