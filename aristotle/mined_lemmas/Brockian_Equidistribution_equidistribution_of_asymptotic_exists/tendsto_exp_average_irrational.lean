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
# Equidistribution Of Asymptotic Exists
Category: Brockian (Open Discharge)
Target: Brockian.Equidistribution.equidistribution_of_asymptotic_exists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(Note: this Lean toolchain requires `import` to be the very first command in a file, so the
required header comment appears immediately after the import.)
-/

open Filter MeasureTheory Set Topology
open scoped ENNReal NNReal Real BigOperators

namespace Brockian.Equidistribution

/-- The circle `ℝ / ℤ`, on which we study equidistribution. -/
abbrev Circ : Type := AddCircle (1 : ℝ)

noncomputable instance : IsProbabilityMeasure (volume : Measure Circ) := ⟨by simp⟩

/-- Continuous functions on the (compact) circle are integrable for any finite measure. -/

lemma tendsto_exp_average_irrational (al : ℝ) (hal : Irrational al) (h : ℤ) (hh : h ≠ 0) :
    Tendsto (fun N : ℕ =>
      (∑ n ∈ Finset.range N, Complex.exp (2 * π * Complex.I * h * ((n : ℝ) * al))) / (N : ℂ))
      atTop (𝓝 0) := by
  set z : ℂ := Complex.exp (2 * π * Complex.I * h * al) with hzdef
  have hznorm : ‖z‖ = 1 := by
    rw [hzdef, Complex.norm_exp]
    norm_num
  have hz1 : z ≠ 1 := by
    rw [hzdef, Ne, Complex.exp_eq_one_iff]
    rintro ⟨k, hk⟩
    have h2pi : (2 : ℂ) * π * Complex.I ≠ 0 := by
      simp [Real.pi_ne_zero, Complex.I_ne_zero]
    have hfac : ((h : ℂ) * al - k) * (2 * π * Complex.I) = 0 := by linear_combination hk
    have hk' : (h : ℂ) * al = (k : ℂ) := by
      rcases mul_eq_zero.mp hfac with h1 | h1
      · exact sub_eq_zero.mp h1
      · exact absurd h1 h2pi
    have hreal : (h : ℝ) * al = (k : ℝ) := by exact_mod_cast hk'
    have hh' : (h : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hh
    refine hal ⟨(k / h : ℚ), ?_⟩
    push_cast
    field_simp at hreal ⊢
    linarith [hreal]
  have hterm : ∀ n : ℕ, Complex.exp (2 * π * Complex.I * h * ((n : ℝ) * al)) = z ^ n := by
    intro n
    rw [hzdef, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hsum : ∀ N : ℕ, ∑ n ∈ Finset.range N,
      Complex.exp (2 * π * Complex.I * h * ((n : ℝ) * al)) = (z ^ N - 1) / (z - 1) := by
    intro N
    simp only [hterm]
    exact geom_sum_eq hz1 N
  have hzpos : (0 : ℝ) < ‖z - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hz1)
  have hbound : ∀ N : ℕ, ‖(∑ n ∈ Finset.range N,
      Complex.exp (2 * π * Complex.I * h * ((n : ℝ) * al))) / (N : ℂ)‖ ≤ (2 / ‖z - 1‖) / N := by
    intro N
    rw [hsum N, norm_div, norm_div, Complex.norm_natCast]
    have h2 : ‖z ^ N - 1‖ ≤ 2 := by
      calc ‖z ^ N - 1‖ ≤ ‖z ^ N‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
        _ = 2 := by rw [norm_pow, hznorm]; norm_num
    gcongr
  exact squeeze_zero_norm hbound (tendsto_const_div_atTop_nhds_zero_nat _)

/-- **Weyl's equidistribution theorem for irrational rotations.**  For irrational `al`, the
sequence `n ↦ n * al` is equidistributed modulo one. -/
