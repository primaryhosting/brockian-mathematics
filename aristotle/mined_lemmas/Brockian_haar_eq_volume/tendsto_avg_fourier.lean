import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

import Mathlib

/-!
# Equidistribution of irrational rotations, and the density of configuration counts

This file proves Weyl's equidistribution theorem for the sequence `n ↦ {n α}` (`α` irrational)
and deduces the unconditional statement `configCount_density_of_BV`: the density of the set of
`n < N` with `{n α} ∈ [a, b)` tends to `b - a`.

The indicator of an interval is the basic example of a function of bounded variation, and the
"BV reduction" is implemented here through the portmanteau theorem: the empirical measures of
the orbit converge weakly to Haar measure (proved via the Fourier/Weyl criterion), hence the
measures of any arc whose boundary is Haar-null converge.
-/

namespace Brockian
namespace EquidistributionBVReduction

open Filter MeasureTheory Set Topology AddCircle
open scoped BigOperators ENNReal NNReal

/-- The point `n • α` of the circle `ℝ / ℤ`. -/

lemma tendsto_avg_fourier {alpha : ℝ} (hirr : Irrational alpha) {k : ℤ} (hk : k ≠ 0) :
    Tendsto (fun N : ℕ => (N : ℂ)⁻¹ * ∑ n ∈ Finset.range N, fourier k (orbitPoint alpha n))
      atTop (𝓝 0) := by
  set z : ℂ := Complex.exp (2 * Real.pi * Complex.I * k * alpha) with hz
  have hzn : ∀ n : ℕ, (fourier k (orbitPoint alpha n) : ℂ) = z ^ n := by
    intro n
    rw [orbitPoint, fourier_coe_apply, hz, ← Complex.exp_nat_mul]
    push_cast
    ring_nf
  have hz1 : z ≠ 1 := by
    intro h
    rw [hz, Complex.exp_eq_one_iff] at h
    obtain ⟨m, hm⟩ := h
    have hpi : (2:ℂ) * Real.pi * Complex.I ≠ 0 := by
      simp [Real.pi_ne_zero, Complex.I_ne_zero]
    have hkm : (k : ℂ) * alpha = m := by
      have : (2 * (Real.pi:ℂ) * Complex.I) * ((k:ℂ) * alpha)
          = (2 * (Real.pi:ℂ) * Complex.I) * m := by
        rw [show (2 * (Real.pi:ℂ) * Complex.I) * ((k:ℂ) * alpha)
            = 2 * (Real.pi:ℂ) * Complex.I * k * alpha by ring, hm]
        ring
      exact mul_left_cancel₀ hpi this
    have hkm' : (k : ℝ) * alpha = m := by exact_mod_cast hkm
    have halpha : alpha = (m : ℝ) / k := by
      field_simp at hkm' ⊢
      linarith [hkm']
    rw [halpha] at hirr
    exact Rat.not_irrational ((m : ℚ)/(k:ℚ))
      (by convert hirr using 2; push_cast; ring)
  have hnorm : ‖z‖ = 1 := by
    rw [hz, Complex.norm_exp]
    simp [Complex.mul_re]
  have hzsub : (0:ℝ) < ‖z - 1‖ := by simpa [sub_eq_zero] using hz1
  simp only [hzn]
  refine squeeze_zero_norm (a := fun N : ℕ => (2 / ‖z - 1‖) / N) (fun N => ?_)
    (tendsto_const_div_atTop_nhds_zero_nat _)
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  have hNpos : (0:ℝ) < N := by exact_mod_cast hN
  have hS : ‖∑ n ∈ Finset.range N, z ^ n‖ ≤ 2 / ‖z - 1‖ := by
    rw [geom_sum_eq hz1 N, norm_div]
    gcongr
    calc ‖z ^ N - 1‖ ≤ ‖z ^ N‖ + ‖(1:ℂ)‖ := norm_sub_le _ _
      _ = 2 := by norm_num [norm_pow, hnorm]
  rw [norm_mul, norm_inv, Complex.norm_natCast, inv_mul_eq_div]
  exact (div_le_div_iff_of_pos_right hNpos).mpr hS

/-- The average of `f` over the first `N` points of the orbit. -/
