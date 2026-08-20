import Mathlib

/-!
# The Fermi–Dirac integral `∫_0^∞ t/(1+e^t) dt = π²/12`

This auxiliary file establishes the elementary integral underlying Mirzakhani's
integration kernel, via the Mellin transform of the Dirichlet eta function.
-/


open Real MeasureTheory Set Complex
open scoped Real

namespace Mirzakhani

/-- Coefficients of the Dirichlet eta series, with the (irrelevant) `n = 0` term set to `0`. -/

lemma integral_id_mul_H_of_nonneg {y : ℝ} (hy : 0 ≤ y) :
    (∫ x in Ioi (0:ℝ), x * H x y) = y ^ 2 / 2 + 2 * π ^ 2 / 3 := by
  have hA : IntegrableOn (fun x : ℝ => x * w (x + y)) (Ioi 0) := by
    refine (integrableOn_affine_mul_w_shift (0:ℝ) 1 0 y).congr_fun ?_ measurableSet_Ioi
    intro x _; ring
  have hB : IntegrableOn (fun x : ℝ => x * w (x + -y)) (Ioi 0) := by
    refine (integrableOn_affine_mul_w_shift (0:ℝ) 1 0 (-y)).congr_fun ?_ measurableSet_Ioi
    intro x _; ring
  have hsplit : (∫ x in Ioi (0:ℝ), x * H x y)
      = (∫ x in Ioi (0:ℝ), x * w (x + y)) + (∫ x in Ioi (0:ℝ), x * w (x + -y)) := by
    rw [← integral_add hA hB]
    exact setIntegral_congr_fun measurableSet_Ioi
      (fun x _ => by simp only [H, sub_eq_add_neg]; ring)
  have hA2 : (∫ x in Ioi (0:ℝ), x * w (x + y)) = ∫ u in Ioi y, (u - y) * w u := by
    have h := integral_Ioi_comp_add_right (fun u => (u - y) * w u) 0 y
    simpa using h
  have hB2 : (∫ x in Ioi (0:ℝ), x * w (x + -y)) = ∫ u in Ioi (-y), (u + y) * w u := by
    have h := integral_Ioi_comp_add_right (fun u => (u + y) * w u) 0 (-y)
    simpa using h
  have hIy : IntegrableOn (fun u => (u + y) * w u) (Ioi (-y)) := by
    refine (integrableOn_affine_mul_w (-y) 1 y).congr_fun ?_ measurableSet_Ioi
    intro u _; ring
  have hsp1 : (∫ u in Ioi (-y), (u + y) * w u)
      = (∫ u in Ioc (-y) y, (u + y) * w u) + (∫ u in Ioi y, (u + y) * w u) :=
    integral_Ioi_split (by linarith) hIy
  have hI0 : IntegrableOn (fun u => u * w u) (Ioi (0:ℝ)) := by
    refine (integrableOn_affine_mul_w (0:ℝ) 1 0).congr_fun ?_ measurableSet_Ioi
    intro u _; ring
  have hsp2 : (∫ u in Ioi (0:ℝ), u * w u)
      = (∫ u in Ioc (0:ℝ) y, u * w u) + (∫ u in Ioi y, u * w u) := integral_Ioi_split hy hI0
  have hIy1 : IntegrableOn (fun u => (u - y) * w u) (Ioi y) := by
    refine (integrableOn_affine_mul_w y 1 (-y)).congr_fun ?_ measurableSet_Ioi
    intro u _; ring
  have hIy2 : IntegrableOn (fun u => (u + y) * w u) (Ioi y) := by
    refine (integrableOn_affine_mul_w y 1 y).congr_fun ?_ measurableSet_Ioi
    intro u _; ring
  have hcomb : (∫ u in Ioi y, (u - y) * w u) + (∫ u in Ioi y, (u + y) * w u)
      = 2 * ∫ u in Ioi y, u * w u := by
    rw [← integral_add hIy1 hIy2, ← MeasureTheory.integral_const_mul]
    exact setIntegral_congr_fun measurableSet_Ioi (fun u _ => by ring)
  have hQ : (∫ u in Ioc (0:ℝ) y, u * w u) = ∫ u in (0:ℝ)..y, u * w u :=
    (intervalIntegral.integral_of_le hy).symm
  have hRc : (∫ u in Ioc (-y) y, (u + y) * w u) = ∫ u in (-y)..y, (u + y) * w u :=
    (intervalIntegral.integral_of_le (by linarith)).symm
  have hR : (∫ u in (-y)..y, (u + y) * w u) = 2 * (∫ u in (0:ℝ)..y, u * w u) + y ^ 2 / 2 := by
    have e1 : (∫ u in (-y)..y, (u + y) * w u)
        = (∫ u in (-y)..y, u * w u) + y * (∫ u in (-y)..y, w u) := by
      rw [← intervalIntegral.integral_const_mul,
        ← intervalIntegral.integral_add (intervalIntegrable_id_mul_w _ _)
          ((intervalIntegrable_w _ _).const_mul y)]
      exact intervalIntegral.integral_congr (fun u _ => by ring)
    rw [e1, integral_symm_w, integral_symm_id_mul_w]; ring
  have hbase := integral_id_mul_w
  rw [hQ] at hsp2
  rw [hsplit, hA2, hB2, hsp1, hRc, hR]
  linarith

/-- **The basic Mirzakhani moment integral**: `∫_0^∞ x H(x,y) dx = y²/2 + 2π²/3`. -/
