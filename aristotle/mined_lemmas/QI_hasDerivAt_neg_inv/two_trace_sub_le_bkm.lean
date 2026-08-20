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
# Scalar integrals used in the integral representations
-/

open MeasureTheory Set Filter
open scoped BigOperators Topology

namespace QI


theorem two_trace_sub_le_bkm (hω : ω.PosDef) (hΔ : Δ.IsHermitian) {A : Mat n}
    (hA : A.IsHermitian) : 2 * (Δ * A).trace.re - (ω * A * A).trace.re ≤ bkm ω Δ := by
  classical
  set d : Fin n → Fin n → ℂ := fun i j => cj hω Δ i j with hd
  set a : Fin n → Fin n → ℂ := fun i j => cj hω A i j with ha
  set μ : Fin n → ℝ := eigV hω with hμ
  have hμpos : ∀ i, 0 < μ i := eigV_pos hω
  have haH : ∀ i j, a j i = (starRingEnd ℂ) (a i j) := fun i j =>
    ((cj_isHermitian hω hA).apply j i).symm
  -- the two traces, in the eigenbasis
  have h1 : (Δ * A).trace.re = ∑ i, ∑ j, (d i j * (starRingEnd ℂ) (a i j)).re := by
    rw [trace_mul_eq_sum_cj hω]
    simp only [← hd, ← ha]
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Complex.re_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [haH i j]
  have h2 : (ω * A * A).trace.re = ∑ i, ∑ j, μ i * ‖a i j‖ ^ 2 := by
    rw [trace_omega_sq hω hA, Complex.ofReal_re]
  -- symmetrization of the quadratic term
  have hcsym : ∀ i j, ‖a i j‖ = ‖a j i‖ := by
    intro i j
    rw [haH i j, RCLike.norm_conj]
  have hsym : ∑ i, ∑ j, μ i * ‖a i j‖ ^ 2 = ∑ i, ∑ j, ((μ i + μ j) / 2) * ‖a i j‖ ^ 2 := by
    have hswap : ∑ i, ∑ j, μ i * ‖a i j‖ ^ 2 = ∑ i, ∑ j, μ j * ‖a i j‖ ^ 2 := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      rw [hcsym j i]
    have expand : ∀ i, ∑ j, ((μ i + μ j) / 2) * ‖a i j‖ ^ 2
        = (∑ j, μ i * ‖a i j‖ ^ 2) / 2 + (∑ j, μ j * ‖a i j‖ ^ 2) / 2 := by
      intro i
      rw [Finset.sum_div, Finset.sum_div, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => expand i), Finset.sum_add_distrib,
      ← Finset.sum_div, ← Finset.sum_div, ← hswap]
    ring
  rw [h1, h2, hsym, bkm_eq_sum hω hΔ]
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_le_sum fun j _ => ?_
  -- the scalar inequality
  have hm : 0 < (μ i + μ j) / 2 := by linarith [hμpos i, hμpos j]
  have hk : 2 / (μ i + μ j) ≤ ∫ t in Ioi (0:ℝ), (μ i + t)⁻¹ * (μ j + t)⁻¹ :=
    two_div_add_le_integral_resProd (hμpos i) (hμpos j)
  have hre : (d i j * (starRingEnd ℂ) (a i j)).re ≤ ‖d i j‖ * ‖a i j‖ := by
    calc (d i j * (starRingEnd ℂ) (a i j)).re ≤ ‖d i j * (starRingEnd ℂ) (a i j)‖ :=
          Complex.re_le_norm _
      _ = ‖d i j‖ * ‖a i j‖ := by rw [norm_mul, RCLike.norm_conj]
  have hamgm : 2 * (‖d i j‖ * ‖a i j‖) - ((μ i + μ j) / 2) * ‖a i j‖ ^ 2
      ≤ ‖d i j‖ ^ 2 * (2 / (μ i + μ j)) := by
    have h2m : 2 / (μ i + μ j) = 1 / ((μ i + μ j) / 2) := by
      rw [one_div_div]
    rw [h2m, mul_one_div, le_div_iff₀ hm]
    nlinarith [sq_nonneg (‖d i j‖ - ((μ i + μ j) / 2) * ‖a i j‖)]
  have hfinal : ‖d i j‖ ^ 2 * (2 / (μ i + μ j))
      ≤ ‖d i j‖ ^ 2 * (∫ t in Ioi (0:ℝ), (μ i + t)⁻¹ * (μ j + t)⁻¹) := by
    exact mul_le_mul_of_nonneg_left hk (by positivity)
  calc 2 * (d i j * (starRingEnd ℂ) (a i j)).re - ((μ i + μ j) / 2) * ‖a i j‖ ^ 2
      ≤ 2 * (‖d i j‖ * ‖a i j‖) - ((μ i + μ j) / 2) * ‖a i j‖ ^ 2 := by linarith
    _ ≤ ‖d i j‖ ^ 2 * (2 / (μ i + μ j)) := hamgm
    _ ≤ _ := hfinal

end QI

import RequestProject.QI.Bkm

/-!
# Measurement: the classical Fisher-type quantity is dominated by the BKM form
-/

open Matrix MeasureTheory Set
open scoped ComplexOrder BigOperators

namespace QI

variable {n : ℕ} {ω Δ : Mat n} {Y : Type*} [Fintype Y] {E : Y → Mat n}

/-- The trace of `ω F` in the eigenbasis of `ω`. -/
