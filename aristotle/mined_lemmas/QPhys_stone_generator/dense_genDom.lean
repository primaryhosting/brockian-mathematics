/-
# Stone Generator
Category: Quantum Physics
Target: QPhys.stone_generator
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Stone Generator
Category: Quantum Physics
Target: QPhys.stone_generator
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

## Contents

Mathlib (as of this version) contains no form of Stone's theorem on one-parameter unitary
groups, so the generator, its domain, and the proof of self-adjointness are developed here
from scratch.  The Mathlib inputs used are the fundamental theorem of calculus for
Banach-space valued interval integrals (`intervalIntegral.integral_hasDerivAt_right`,
`intervalIntegral.integral_eq_sub_of_hasDerivAt`), the fact that continuous linear maps
commute with interval integrals (`ContinuousLinearMap.intervalIntegral_comp_comm`),
differentiability of the inner product (`HasDerivAt.inner`), and
`Dense.eq_of_inner_right`.
-/

namespace QPhys

open Complex MeasureTheory intervalIntegral
open scoped Classical

section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The domain of the generator of a one-parameter group `U : ℝ → H →L[ℂ] H`:
the set of vectors `x` for which `t ↦ U t x` is differentiable at `0`.  We write the
derivative as `Complex.I • z`, so that `U t = exp (t • (I • A))`, i.e. `A` is the
"physicist's" generator (`U t = exp (i t A)`). -/

theorem dense_genDom : Dense (genDom U : Set H) := by
  intro x
  rw [Metric.mem_closure_iff]
  intro ε hε
  have hcx : Continuous fun s => U s x := hcont x
  have hint : ∀ b c : ℝ, IntervalIntegrable (fun s => U s x) volume b c := fun b c =>
    hcx.intervalIntegrable b c
  obtain ⟨δ, hδ, hball⟩ :=
    Metric.continuousAt_iff.1 (hcx.continuousAt (x := (0:ℝ))) (ε / 2) (by positivity)
  set a : ℝ := δ / 2 with ha
  have ha0 : 0 < a := by positivity
  refine ⟨((a : ℂ)⁻¹ • (∫ s in (0:ℝ)..a, U s x) : H), ?_, ?_⟩
  · exact Submodule.smul_mem _ _ (average_mem_genDom h0 hadd hcont x a)
  · have hane : (a : ℂ) ≠ 0 := by
      simp only [ne_eq, Complex.ofReal_eq_zero]
      exact ne_of_gt ha0
    have hsplit : (∫ s in (0:ℝ)..a, U s x) - (a : ℂ) • x = ∫ s in (0:ℝ)..a, (U s x - x) := by
      rw [intervalIntegral.integral_sub (hint 0 a) (intervalIntegrable_const)]
      have : (∫ _s in (0:ℝ)..a, x) = (a - 0) • x := intervalIntegral.integral_const x
      rw [this]
      congr 1
      simp
    have hbound : ‖∫ s in (0:ℝ)..a, (U s x - x)‖ ≤ (ε / 2) * |a - 0| := by
      refine intervalIntegral.norm_integral_le_of_norm_le_const ?_
      intro s hs
      rw [Set.uIoc_of_le ha0.le] at hs
      have hds : dist s 0 < δ := by
        rw [Real.dist_eq, sub_zero, abs_of_pos hs.1]
        exact lt_of_le_of_lt hs.2 (by rw [ha]; linarith)
      have := hball hds
      rw [h0] at this
      simpa [dist_eq_norm] using this.le
    have hkey : (a : ℂ)⁻¹ • (∫ s in (0:ℝ)..a, U s x) - x
        = (a : ℂ)⁻¹ • ((∫ s in (0:ℝ)..a, U s x) - (a : ℂ) • x) := by
      rw [smul_sub, smul_smul, inv_mul_cancel₀ hane, one_smul]
    rw [dist_comm, dist_eq_norm, hkey, hsplit, norm_smul]
    have hnorm_inv : ‖(a : ℂ)⁻¹‖ = a⁻¹ := by
      simp [abs_of_pos ha0]
    rw [hnorm_inv]
    have : a⁻¹ * ‖∫ s in (0:ℝ)..a, (U s x - x)‖ ≤ a⁻¹ * ((ε / 2) * |a - 0|) := by
      exact mul_le_mul_of_nonneg_left hbound (by positivity)
    have hfin : a⁻¹ * ((ε / 2) * |a - 0|) = ε / 2 := by
      rw [sub_zero, abs_of_pos ha0]
      field_simp
    calc a⁻¹ * ‖∫ s in (0:ℝ)..a, (U s x - x)‖ ≤ a⁻¹ * ((ε / 2) * |a - 0|) := this
      _ = ε / 2 := hfin
      _ < ε := by linarith

include h0 hadd hnorm hcont in
/-- Self-adjointness: any vector in the domain of the adjoint is in the domain of the
generator. -/
