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


theorem abs_trace_res_quad_le (hω : ω.PosDef) {m t : ℝ} (hm : ∀ i, m ≤ eigV hω i) (ht : 0 ≤ t)
    (hmt : 0 < m + t) (A B : Mat n) :
    |(A * res ω t * B * res ω t).trace.re|
      ≤ (frobSq A + frobSq B) / 2 * ((m + t)⁻¹ * (m + t)⁻¹) := by
  have hrle : ∀ i, (eigV hω i + t)⁻¹ ≤ (m + t)⁻¹ := by
    intro i
    have h1 : 0 < m + t := hmt
    have h2 : m + t ≤ eigV hω i + t := by linarith [hm i]
    exact inv_anti₀ h1 h2
  have hrnn : ∀ i, 0 ≤ (eigV hω i + t)⁻¹ := by
    intro i
    have : 0 < eigV hω i + t := by linarith [eigV_pos hω i]
    positivity
  rw [trace_res_quad hω ht A B]
  set a : Fin n → Fin n → ℂ := fun i j => cj hω A i j with ha
  set b : Fin n → Fin n → ℂ := fun i j => cj hω B i j with hb
  calc |(∑ i, ∑ j, a i j * (((eigV hω j + t)⁻¹ : ℝ) : ℂ) * b j i
            * (((eigV hω i + t)⁻¹ : ℝ) : ℂ)).re|
      ≤ ‖∑ i, ∑ j, a i j * (((eigV hω j + t)⁻¹ : ℝ) : ℂ) * b j i
            * (((eigV hω i + t)⁻¹ : ℝ) : ℂ)‖ := Complex.abs_re_le_norm _
    _ ≤ ∑ i, ∑ j, ‖a i j‖ * ‖b j i‖ * ((eigV hω j + t)⁻¹ * (eigV hω i + t)⁻¹) := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
        refine le_of_eq ?_
        rw [norm_mul, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
          Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (hrnn i), abs_of_nonneg (hrnn j)]
        ring
    _ ≤ ∑ i, ∑ j, ‖a i j‖ * ‖b j i‖ * ((m + t)⁻¹ * (m + t)⁻¹) := by
        refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
        have hnn : 0 ≤ ‖a i j‖ * ‖b j i‖ := by positivity
        have hstep : (eigV hω j + t)⁻¹ * (eigV hω i + t)⁻¹ ≤ (m + t)⁻¹ * (m + t)⁻¹ :=
          mul_le_mul (hrle j) (hrle i) (hrnn i) (le_of_lt (inv_pos.mpr hmt))
        exact mul_le_mul_of_nonneg_left hstep hnn
    _ = (∑ i, ∑ j, ‖a i j‖ * ‖b j i‖) * ((m + t)⁻¹ * (m + t)⁻¹) := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun i _ => (Finset.sum_mul _ _ _).symm
    _ ≤ (frobSq A + frobSq B) / 2 * ((m + t)⁻¹ * (m + t)⁻¹) := by
        have hsum : ∑ i, ∑ j, ‖a i j‖ * ‖b j i‖ ≤ (frobSq A + frobSq B) / 2 := by
          have hstep : ∀ i, ∑ j, ‖a i j‖ * ‖b j i‖
              ≤ ∑ j, (‖a i j‖ ^ 2 / 2 + ‖b j i‖ ^ 2 / 2) := by
            intro i
            refine Finset.sum_le_sum fun j _ => ?_
            nlinarith [sq_nonneg (‖a i j‖ - ‖b j i‖)]
          have h1 : ∑ i, ∑ j, ‖a i j‖ * ‖b j i‖
              ≤ ∑ i, ∑ j, (‖a i j‖ ^ 2 / 2 + ‖b j i‖ ^ 2 / 2) :=
            Finset.sum_le_sum fun i _ => hstep i
          have hA2 : ∑ i, ∑ j, ‖a i j‖ ^ 2 / 2 = frobSq (cj hω A) / 2 := by
            rw [frobSq, Finset.sum_div]
            exact Finset.sum_congr rfl fun i _ => (Finset.sum_div _ _ _).symm
          have hB2 : ∑ i, ∑ j, ‖b j i‖ ^ 2 / 2 = frobSq (cj hω B) / 2 := by
            rw [Finset.sum_comm, frobSq, Finset.sum_div]
            exact Finset.sum_congr rfl fun i _ => (Finset.sum_div _ _ _).symm
          have h2 : ∑ i, ∑ j, (‖a i j‖ ^ 2 / 2 + ‖b j i‖ ^ 2 / 2)
              = frobSq (cj hω A) / 2 + frobSq (cj hω B) / 2 := by
            rw [← hA2, ← hB2, ← Finset.sum_add_distrib]
            exact Finset.sum_congr rfl fun i _ => Finset.sum_add_distrib
          rw [h2, frobSq_cj, frobSq_cj] at h1
          linarith
        have hpos : 0 ≤ (m + t)⁻¹ * (m + t)⁻¹ := by positivity
        exact mul_le_mul_of_nonneg_right hsum hpos

end QI

import RequestProject.QI.Defs

/-!
# Spectral tools

Elementary facts about unitary conjugation and the functional calculus of Hermitian matrices,
used to compute traces in an eigenbasis.
-/

open Matrix
open scoped ComplexOrder BigOperators

namespace QI

variable {n : ℕ}

/-- Conjugation of a matrix by a unitary preserves the trace. -/
