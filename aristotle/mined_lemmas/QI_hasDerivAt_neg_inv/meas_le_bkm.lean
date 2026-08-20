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


theorem meas_le_bkm (hω : ω.PosDef) (hΔ : Δ.IsHermitian) (hE : IsPOVM E) :
    ∑ y, ((Δ * E y).trace.re) ^ 2 / ((ω * E y).trace.re) ≤ bkm ω Δ := by
  classical
  set w : Y → ℝ := fun y => (ω * E y).trace.re with hw
  set d : Y → ℝ := fun y => (Δ * E y).trace.re with hd
  set c : Y → ℝ := fun y => d y / w y with hc
  set A : Mat n := ∑ y, ((c y : ℝ) : ℂ) • E y with hAdef
  have hEzero : ∀ y, w y = 0 → E y = 0 := fun y h =>
    eq_zero_of_trace_mul_eq_zero hω (hE.posSemidef y) h
  have hdzero : ∀ y, w y = 0 → d y = 0 := by
    intro y h
    simp [hd, hEzero y h]
  have hAherm : A.IsHermitian := by
    have hherm : ∀ y, (E y)ᴴ = E y := fun y => (hE.posSemidef y).isHermitian
    show Aᴴ = A
    rw [hAdef]
    simp [Matrix.conjTranspose_sum, Matrix.conjTranspose_smul, hherm]
  -- the linear term
  have e1 : ∀ y, c y * d y = d y ^ 2 / w y := by
    intro y
    by_cases h : w y = 0
    · simp [hc, h, hdzero y h]
    · simp only [hc]
      field_simp
  have hlin : (Δ * A).trace.re = ∑ y, d y ^ 2 / w y := by
    rw [hAdef, trace_mul_sum_smul]
    exact Finset.sum_congr rfl fun y _ => e1 y
  -- the quadratic term
  have e2 : ∀ y, c y ^ 2 * w y = d y ^ 2 / w y := by
    intro y
    by_cases h : w y = 0
    · simp [hc, h, hdzero y h]
    · simp only [hc]
      field_simp
  have hquad : (ω * A * A).trace.re ≤ ∑ y, d y ^ 2 / w y := by
    have hpsd := trace_mul_nonneg hω (povm_sq_le hE c)
    have hsplit : (ω * ((∑ y, ((c y ^ 2 : ℝ) : ℂ) • E y) - A * A)).trace.re
        = (ω * ∑ y, ((c y ^ 2 : ℝ) : ℂ) • E y).trace.re - (ω * (A * A)).trace.re := by
      rw [Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re]
    rw [hsplit, trace_mul_sum_smul] at hpsd
    have : (ω * (A * A)).trace.re ≤ ∑ y, c y ^ 2 * w y := by linarith
    rw [← Matrix.mul_assoc] at this
    refine this.trans (le_of_eq (Finset.sum_congr rfl fun y _ => e2 y))
  have key := two_trace_sub_le_bkm hω hΔ hAherm
  rw [hlin] at key
  linarith

end QI

import RequestProject.QI.Estimates

/-!
# The integral representation of the relative entropy

The Umegaki relative entropy of two faithful states of equal trace is
`D(ρ‖σ) = ∫₀¹ (1-s) · bkm (σ + s(ρ-σ)) (ρ-σ) ds`.
-/

open Matrix MeasureTheory Set
open scoped ComplexOrder BigOperators

namespace QI

variable {n : ℕ} {ω ρ σ : Mat n}

/-- The interpolating path `ω s = σ + s (ρ - σ) = (1-s) σ + s ρ`. -/
