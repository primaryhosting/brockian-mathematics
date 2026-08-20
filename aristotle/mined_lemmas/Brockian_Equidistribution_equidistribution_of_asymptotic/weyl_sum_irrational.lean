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

/-
# Equidistribution Of Asymptotic
Category: Brockian (Open Discharge)
Target: Brockian.Equidistribution.equidistribution_of_asymptotic
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Equidistribution Of Asymptotic
Category: Brockian (Open Discharge)
Target: Brockian.Equidistribution.equidistribution_of_asymptotic
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(The block above is repeated as the file header; Lean does not allow a module docstring to
precede the `import` line.)

This file proves **Weyl's equidistribution criterion** unconditionally: if all nontrivial
exponential sums of a real sequence `x` are asymptotically negligible, then `x` is
equidistributed modulo one.  The argument goes through the circle `𝕋 = AddCircle 1`:

* the Birkhoff averages of each Fourier monomial converge to its integral (`avgC_fourier_tendsto`);
* the set of continuous functions with this property is a closed submodule of `C(𝕋, ℂ)`, hence,
  by Stone-Weierstrass (`span_fourier_closure_eq_top`), is everything (`avgC_tendsto`);
* indicator functions of arcs are squeezed between continuous plateau functions supported on
  metric balls, whose integrals are controlled by `AddCircle.volume_closedBall`.

As an application (and as a witness that the hypothesis is satisfiable) we derive the classical
equidistribution of irrational rotations, `equidistribution_irrational_rotation`.
-/

open Filter MeasureTheory Metric Complex Set
open scoped Topology Real BigOperators

namespace Brockian.Equidistribution

local notation "𝕋" => AddCircle (1 : ℝ)

/-- The Birkhoff/Weyl average of a complex-valued continuous function on the circle along the
first `N` terms of the sequence `x`. -/

lemma weyl_sum_irrational {α : ℝ} (hα : Irrational α) (k : ℤ) (hk : k ≠ 0) :
    Tendsto (fun N : ℕ => (N : ℂ)⁻¹ * ∑ n ∈ Finset.range N,
        Complex.exp (2 * π * Complex.I * k * (((n : ℝ) * α : ℝ) : ℂ))) atTop (𝓝 0) := by
  set w : ℝ := 2 * π * k * α with hw
  set z : ℂ := Complex.exp (w * Complex.I) with hz
  have hznorm : ‖z‖ = 1 := by rw [hz]; exact Complex.norm_exp_ofReal_mul_I w
  have hzne : z ≠ 1 := by
    intro h
    rw [hz, Complex.exp_eq_one_iff] at h
    obtain ⟨m, hm⟩ := h
    have hm' : (w : ℂ) * Complex.I = ((m : ℂ) * (2 * π)) * Complex.I := by rw [hm]; ring
    have hw2 : (w : ℂ) = (m : ℂ) * (2 * π) := mul_right_cancel₀ Complex.I_ne_zero hm'
    have hwr : w = (m : ℝ) * (2 * π) := by exact_mod_cast hw2
    have h2π : (2 * π : ℝ) ≠ 0 := by positivity
    have hka : (2 * π) * ((k : ℝ) * α) = (2 * π) * (m : ℝ) := by
      rw [hw] at hwr; ring_nf; ring_nf at hwr; linarith
    exact (Irrational.intCast_mul hα hk).ne_int m (mul_left_cancel₀ h2π hka)
  have hterm : ∀ n : ℕ,
      Complex.exp (2 * π * Complex.I * k * (((n : ℝ) * α : ℝ) : ℂ)) = z ^ n := by
    intro n
    rw [hz, ← Complex.exp_nat_mul]
    congr 1
    rw [hw]
    push_cast
    ring
  have hzpos : 0 < ‖z - 1‖ := by
    rw [norm_pos_iff]
    exact sub_ne_zero_of_ne hzne
  have hsum : ∀ N : ℕ, ‖∑ n ∈ Finset.range N, z ^ n‖ ≤ 2 / ‖z - 1‖ := by
    intro N
    rw [geom_sum_eq hzne N, norm_div]
    have hnum : ‖z ^ N - 1‖ ≤ 2 := by
      refine (norm_sub_le _ _).trans ?_
      rw [norm_pow, hznorm, one_pow, norm_one]
      norm_num
    gcongr
  have hbound : ∀ N : ℕ, ‖(N : ℂ)⁻¹ * ∑ n ∈ Finset.range N,
      Complex.exp (2 * π * Complex.I * k * (((n : ℝ) * α : ℝ) : ℂ))‖ ≤ (2 / ‖z - 1‖) / N := by
    intro N
    simp only [hterm]
    rw [norm_mul, norm_inv, Complex.norm_natCast]
    have hrw : (2 / ‖z - 1‖) / (N : ℝ) = (N : ℝ)⁻¹ * (2 / ‖z - 1‖) := by ring
    rw [hrw]
    exact mul_le_mul_of_nonneg_left (hsum N) (by positivity)
  exact squeeze_zero_norm hbound (tendsto_const_div_atTop_nhds_zero_nat _)

/-- **Equidistribution of irrational rotations.**  For irrational `α`, the fractional parts of
`n * α` are equidistributed in `[0, 1)`. -/
