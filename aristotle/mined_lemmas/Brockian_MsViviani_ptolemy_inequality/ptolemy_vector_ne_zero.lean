import Mathlib
namespace Brockian.MsViviani

/-- The inversion map `x ↦ ‖x‖⁻² • x` scales distances by `(‖x‖ * ‖y‖)⁻¹`. -/

private lemma ptolemy_vector_ne_zero {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (a b c : E) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) :
    ‖a - c‖ * ‖b‖ ≤ ‖a - b‖ * ‖c‖ + ‖b - c‖ * ‖a‖ := by
  have ha' : (0:ℝ) < ‖a‖ := norm_pos_iff.mpr ha
  have hb' : (0:ℝ) < ‖b‖ := norm_pos_iff.mpr hb
  have hc' : (0:ℝ) < ‖c‖ := norm_pos_iff.mpr hc
  -- triangle inequality for the inverted points
  have htri : ‖(‖a‖ ^ 2)⁻¹ • a - (‖c‖ ^ 2)⁻¹ • c‖ ≤
      ‖(‖a‖ ^ 2)⁻¹ • a - (‖b‖ ^ 2)⁻¹ • b‖ + ‖(‖b‖ ^ 2)⁻¹ • b - (‖c‖ ^ 2)⁻¹ • c‖ :=
    norm_sub_le_norm_sub_add_norm_sub _ _ _
  rw [norm_inversion_sub_inversion a c ha hc, norm_inversion_sub_inversion a b ha hb,
    norm_inversion_sub_inversion b c hb hc] at htri
  -- multiply through by ‖a‖ * ‖b‖ * ‖c‖
  have hmul := mul_le_mul_of_nonneg_left htri
    (le_of_lt (mul_pos (mul_pos ha' hb') hc'))
  calc ‖a - c‖ * ‖b‖
      = ‖a‖ * ‖b‖ * ‖c‖ * (‖a - c‖ / (‖a‖ * ‖c‖)) := by field_simp
    _ ≤ ‖a‖ * ‖b‖ * ‖c‖ * (‖a - b‖ / (‖a‖ * ‖b‖) + ‖b - c‖ / (‖b‖ * ‖c‖)) := hmul
    _ = ‖a - b‖ * ‖c‖ + ‖b - c‖ * ‖a‖ := by field_simp

/-- Ptolemy's inequality, vector form: for `a b c` in a real inner product space,
    `‖a - c‖ * ‖b‖ ≤ ‖a - b‖ * ‖c‖ + ‖b - c‖ * ‖a‖`. -/
